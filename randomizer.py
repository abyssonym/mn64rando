from randomtools.tablereader import (
    TableObject, get_global_label, addresses, names, gen_random_normal,
    get_activated_patches, mutate_normal, shuffle_normal, write_patch,
    get_random_degree, tblpath, get_open_file)
from randomtools.utils import (
    classproperty, cached_property, utilrandom as random)
from randomtools.interface import (
    get_outfile, get_seed, get_flags, get_activated_codes, activate_code,
    run_interface, rewrite_snes_meta, clean_and_write, finish_interface)

from collections import Counter, defaultdict
from time import time, gmtime
from itertools import combinations
from os import path
from traceback import format_exc
import re
import yaml

from decompress_mn64 import decompress_from_file, recompress


VERSION = "0"
ALL_OBJECTS = None
DEBUG_MODE = False


def hexify(s):
    result = []
    while s:
        w = s[:4]
        s = s[4:]
        w = ' '.join('{0:0>2x}'.format(c) for c in w)
        result.append(w)
    return ' '.join(result)


def pretty_hexify(s):
    result = []
    while s:
        line, s = s[:0x10], s[0x10:]
        line_result = []
        while line:
            word, line = line[:4], line[4:]
            line_result.append(hexify(word))
        result.append('  '.join(line_result))
    return '\n'.join(result)


class MapMetaObject(TableObject):
    ENTITY_STRUCTURES_FILENAME = path.join(tblpath, 'entity_structures.yaml')
    with open(ENTITY_STRUCTURES_FILENAME) as f:
        entity_structures = yaml.load(f.read(),
                                      Loader=yaml.SafeLoader)

    structure_names = set()
    for index, structure in entity_structures.items():
        name = structure['name']
        if name in structure_names:
            raise Exception(f'Duplicate structure name: {name}')
        structure_names.add(name)

    class EntityMixin:
        DICT_MATCHER = re.compile('{[^}]*}')

        def __init__(self, data, parent, index=None):
            assert len(data) == self.DATA_LENGTH
            self.parent = parent
            if index is None:
                if self.parent.entities:
                    self.index = max(e.index for e in self.parent.entities) + 1
                else:
                    self.index = 0
            else:
                self.index = index
            self.data = data
            self.old_data = data
            self.validate_data()

        def __repr__(self):
            details = self.details
            if details is not None:
                s = '{0}  @ {1}'.format(self.hexify(), self.details)
            else:
                s = self.hexify()
            if self.comment:
                s = f'  # {self.comment}\n{s}'
            return s

        @property
        def is_null(self):
            return set(self.data) == {0}

        @property
        def comment(self):
            return None

        def hexify(self):
            return f'{self.index:0>3x}: {hexify(self.data)}'

        def validate_data(self):
            return

        def get_property_indexes(self, property_name):
            data = self.structure[property_name]
            index = data['index']
            if isinstance(index, int):
                start = index
                finish = index + 1
            else:
                start, finish = index
                finish += 1
            assert finish > start
            return start, finish

        def get_property_value(self, property_name):
            start, finish = self.get_property_indexes(property_name)
            value = int.from_bytes(self.data[start:finish],
                                   byteorder='big')
            return value

        def set_property(self, property_name, value):
            data = self.structure[property_name]
            start, finish = self.get_property_indexes(property_name)
            if isinstance(value, str):
                if '-' in value:
                    value = value.split('-')[0]
                value = int(value, 0x10)
            value_length = finish - start
            value = value.to_bytes(length=value_length, byteorder='big')
            data = self.data[:start] + value + self.data[finish:]
            assert len(data) == len(self.data)
            self.data = data

        def import_details(self, details):
            dict_matches = self.DICT_MATCHER.findall(details)
            for match in dict_matches:
                details = details.replace(match, '')
                assert match[0] == '{'
                assert match[-1] == '}'
                match = match[1:-1]
                properties = match.split(',')
                for prop in properties:
                    key, value = prop.split(':')
                    self.set_property(key, value)
            assert '{' not in details and '}' not in details
            details = details.strip()
            if details:
                self.set_main_actor(details)

    class EntityDefinition(EntityMixin):
        DATA_LENGTH = 0x10

        @property
        def actor_id(self):
            return int.from_bytes(self.data[:2], byteorder='big')

        @property
        def structure(self):
            if self.actor_id not in MapMetaObject.entity_structures:
                return None
            return MapMetaObject.entity_structures[self.actor_id]

        @property
        def details(self):
            if not self.structure:
                return None

            unsorted_details = []
            for property_name, data in self.structure.items():
                if property_name == 'name':
                    continue

                start, finish = self.get_property_indexes(property_name)
                value = self.get_property_value(property_name)
                pretty_value = ('{0:0>%sx}' % ((finish-start)*2)).format(value)
                if value in data:
                    pretty_value = f'{pretty_value}-{data[value]}'

                unsorted_details.append((start, property_name, pretty_value))
            details = [f'{p}:{v}' for (s, p, v) in sorted(unsorted_details)]
            if details:
                details = '{%s}' % (','.join(details))
                return '{0} {1}'.format(self.structure['name'], details)
            else:
                return self.structure['name']

        def set_main_actor(self, name):
            for actor_id, data in MapMetaObject.entity_structures.items():
                if data['name'] == name:
                    actor_id = actor_id.to_bytes(length=2, byteorder='big')
                    data = actor_id + self.data[2:]
                    assert len(data) == len(self.data)
                    self.data = data
                    break
            else:
                raise Exception('Could not find actor "%s".' % name)

        def validate_data(self):
            return
            assert self.data[:2] != b'\x00\x00'
            assert self.data[1] != 0

    class EntityInstance(EntityMixin):
        DATA_LENGTH = 0x14

        structure = {'definition_index':    {'index': (0xe, 0xf)},
                     'x':                   {'index': (0x0, 0x1)},
                     'z':                   {'index': (0x2, 0x3)},
                     'y':                   {'index': (0x4, 0x5)},
                     }

        @property
        def definition_index(self):
            return self.get_property_value('definition_index') >> 4

        @property
        def x(self):
            return self.get_property_value('x')

        @property
        def z(self):
            return self.get_property_value('z')

        @property
        def y(self):
            return self.get_property_value('y')

        @property
        def definition(self):
            if self.is_null:
                return None
            if self in self.parent.entities[-2:]:
                return None
            if self.definition_index >= len(self.parent.entities):
                return None
            definition = self.parent.entities[self.definition_index]
            if isinstance(definition, MapMetaObject.EntityDefinition):
                return definition
            return None

        @property
        def details(self):
            if self.is_null:
                return None
            if not self.definition:
                return None
            details = []
            for key in ['x', 'z', 'y']:
                value = f'{getattr(self, key):0>4x}'
                details.append(f'{key}:{value}')
            details = '{%s}' % ','.join(details)
            return f'{self.definition_index:0>3x} {details}'

        @property
        def comment(self):
            if not self.definition:
                return
            return self.definition.details

        def validate_data(self):
            #assert self.data[0xf] & 0xf == 0
            return
            assert self.data[-4:] == b'\x00\x00\x00\x00'
            assert self.data[1] == 0

        def set_main_actor(self, name):
            self.set_property('definition_index', int(name, 0x10) << 4)
            assert self.definition_index == int(name, 0x10)

    @classmethod
    def import_from_file(self, filename):
        mmo = None
        with open(filename) as f:
            for line in f:
                if '#' in line:
                    line = line.split('#')[0]
                line = line.strip()
                if not line:
                    continue
                while '  ' in line:
                    line = line.replace('  ', ' ')
                if line.startswith('ROOM '):
                    if ':' in line:
                        line = line.split(':')[0]
                    room_index = int(line[5:], 0x10)
                    mmo = MapMetaObject.get(room_index)
                    continue
                if line.startswith('LEFTOVER'):
                    mmo.leftover_data = b''
                    continue
                if ':' in line:
                    mmo.import_line(line)
                    continue
                line = bytes([int(v, 0x10) for v in line.split()])
                mmo.leftover_data += line

    @classmethod
    def consolidate_free_space(self):
        free_space = sorted(MapMetaObject.free_space)
        while True:
            terminate_done = True
            for (a1, b1) in list(free_space):
                if not terminate_done:
                    break
                for (a2, b2) in list(free_space):
                    if (a1, b1) == (a2, b2):
                        continue
                    if a1 <= a2 <= b1 or a1 <= b2 <= b1:
                        free_space.remove((a1, b1))
                        free_space.remove((a2, b2))
                        new_pair = (min(a1, a2), max(b1, b2))
                        free_space.append(new_pair)
                        terminate_done = False
                        break
            if terminate_done:
                break
        MapMetaObject.free_space = sorted(free_space)

    @classmethod
    def allocate(self, length):
        length += 3
        candidates = [(a, b) for (a, b) in self.free_space if b-a >= length]
        assert candidates
        candidates = sorted(candidates, key=lambda x: (x[1]-x[0], x))
        (start, finish) = candidates[0]
        MapMetaObject.free_space.remove((start, finish))
        new_start = start+length
        if length != 0:
            assert start < new_start <= finish
        if new_start < finish:
            MapMetaObject.free_space.append((new_start, finish))
            MapMetaObject.free_space = sorted(MapMetaObject.free_space)
        while start % 4:
            start += 1
        return start

    def __repr__(self):
        header = (f'ROOM {self.index:0>3X}: {self.pointer:0>5x} -> '
                  f'{self.reference_pointer:0>8x}')
        s = header + '\n' + self.hexify()
        s = s.replace('\n', '\n  ')
        return s.strip()

    @property
    def data_pointer(self):
        return self.reference_pointer & 0x7fffffff

    @property
    def data(self):
        data = b''
        for e in self.entities:
            data += e.data
        if self.leftover_data is not None:
            data += self.leftover_data
        return data

    @property
    def data_has_changed(self):
        if not hasattr(self, '_cached_decompressed'):
            return False
        old_data = self._cached_decompressed
        data = self.data
        while len(data) < len(old_data):
            data += b'\x00'
        while len(old_data) < len(data):
            old_data += b'\x00'
        return data != old_data

    @property
    def is_room_series(self):
        #return 0x58f10 <= self.pointer <= 0x5945f
        return 0x58f2c <= self.pointer <= 0x5945f

    def get_decompressed(self):
        if hasattr(self, '_cached_decompressed'):
            return self._cached_decompressed
        f = get_open_file(get_outfile())
        try:
            data, (start, finish) = decompress_from_file(f, self.data_pointer)
            self._deallocation_start = start
            self._deallocation_finish = finish
        except:
            data = None
        self._cached_decompressed = data
        return self.get_decompressed()

    def get_entities(self):
        if hasattr(self, 'entities'):
            return self.entities

        self.entities = []
        self.leftover_data = None
        data = self.get_decompressed()
        if data is None:
            return None

        entity_type = self.EntityDefinition
        while True:
            if set(data) <= {0}:
                break

            if len(data) > 0xc and data[0xc] == 0x08:
                entity_type = self.EntityInstance

            segment_length = entity_type.DATA_LENGTH
            while len(data) < segment_length:
                data += b'\x00'
            segment, data = data[:segment_length], data[segment_length:]
            entity = entity_type(segment, self)

            if entity_type is self.EntityDefinition and entity.is_null:
                data = segment + data
                entity_type = self.EntityInstance
                continue

            self.entities.append(entity)
            #if entity_type is self.EntityInstance and entity.is_null:
            #    break

        self.leftover_data = data
        assert set(self.leftover_data) <= {0}
        return self.entities

    def hexify(self):
        s = '\n'.join([str(e) for e in self.entities])
        if self.leftover_data:
            leftover = pretty_hexify(self.leftover_data).replace('\n', '\n  ')
            s = f'{s}\nLEFTOVER ({len(self.leftover_data)}):\n  {leftover}'
        return s

    def import_line(self, line):
        if '#' in line:
            line = line.split('#')[0]
        if '@' in line:
            line, details = line.split('@', 1)
            details = details.strip()
        else:
            details = None

        line = line.strip()
        if not line:
            return

        assert ':' in line
        index, line = line.split(':')
        line = line.strip()
        index = int(index, 0x10)
        for e in list(self.entities):
            if e.index == index:
                self.entities.remove(e)

        new_data = bytes([int(v,0x10) for v in line.split()])
        for entity_type in (self.EntityDefinition,
                            self.EntityInstance):
            if len(new_data) == entity_type.DATA_LENGTH:
                break
        else:
            raise Exception('Improper import data length.')

        new_entity = entity_type(new_data, self, index)
        if details is not None:
            new_entity.import_details(details)
        self.entities.append(new_entity)
        self.entities = sorted(self.entities, key=lambda e: e.index)

    def deallocate(self):
        raise Exception('Deallocated data cannot be used. '
                        'Pointers must be in ascending order.')
        start = self._deallocation_start
        finish = self._deallocation_finish
        for mmo in MapMetaObject.every:
            if start < mmo.data_pointer < finish:
                finish = mmo.data_pointer
        if finish <= start:
            return
        MapMetaObject.free_space.append((start, finish))
        self.consolidate_free_space()

    def get_unmodified_compressed(self):
        try:
            start = self._deallocation_start
            finish = self._deallocation_finish
        except AttributeError:
            start = self.reference_pointer & 0x7fffffff
            finish = self.get(self.index+1).reference_pointer & 0x7fffffff
            assert finish > start
        f = get_open_file(get_outfile())
        f.seek(start)
        return f.read(finish-start)

    def compress_and_write(self):
        if self.data_has_changed:
            recomp = recompress(self.data)
        else:
            recomp = self.get_unmodified_compressed()
        while len(recomp) % 4:
            recomp += b'\x00'
        recomp += b'\x00\x00\x00\x00'
        #self.deallocate()
        address = self.allocate(len(recomp))
        f = get_open_file(get_outfile())
        f.seek(address)
        f.write(recomp)
        new_pointer = (self.reference_pointer & 0x80000000) | address
        self.reference_pointer = new_pointer
        self.relocated = True

    def preprocess(self):
        if not hasattr(MapMetaObject, 'free_space'):
            MapMetaObject.free_space = [(addresses.free_space_start,
                                         addresses.free_space_end)]

        self.reference_pointer = int.from_bytes(
            self.reference_pointer_be, byteorder='big')
        self.old_data['reference_pointer'] = self.reference_pointer

        if self.is_room_series:
            self.get_entities()
            assert not self.data_has_changed
            assert self.entities

    def cleanup(self):
        #if self.data_has_changed:
        if self.is_room_series:
            self.compress_and_write()
            # for whatever reason, pointers must be in ascending order
            assert self.relocated
            assert not hasattr(self.get(self.index+1), 'relocated')
            previous = self.get(self.index-1)
            if hasattr(previous, 'relocated'):
                assert previous.reference_pointer <= self.reference_pointer
        self.reference_pointer_be = self.reference_pointer.to_bytes(
            length=4, byteorder='big')


if __name__ == '__main__':
    try:
        print('You are using the MN64 Door Randomizer '
              'randomizer version %s.' % VERSION)

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]

        codes = {
        }

        run_interface(ALL_OBJECTS, snes=False, n64=True, codes=codes,
                      custom_degree=False, custom_difficulty=False)

        #if 'export' in get_activated_codes():
        #    export_all(ALL_OBJECTS)

        for code in sorted(get_activated_codes()):
            print('Code "%s" activated.' % code)

        '''
        for mmo in MapMetaObject.every:
            if not mmo.is_room_series:
                continue
            print(mmo)
            print()
        exit(0)
        '''
        print('IMPORTING')
        MapMetaObject.import_from_file('to_import.txt')
        for mmo in MapMetaObject.every:
            if mmo.data_has_changed:
                print(mmo)

        #print(MapMetaObject.get(0x40b))

        #if 'import' in get_activated_codes():
        #    import_all(ALL_OBJECTS)

        #write_seed()

        clean_and_write(ALL_OBJECTS)
        finish_interface()

    except Exception:
        print('ERROR: %s' % format_exc())
        input('Press Enter to close this program. ')
