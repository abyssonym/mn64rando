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
import yaml

from decompress_mn64 import decompress_from_file


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

    class Entity:
        def __init__(self, data, parent):
            assert len(data) == self.DATA_LENGTH
            self.parent = parent
            self.index = len(self.parent.entities)
            self.data = data
            self.old_data = data
            self.validate_data()

        def __repr__(self):
            return self.hexify()

        @property
        def is_null(self):
            return set(self.data) == {0}

        def hexify(self):
            return f'{self.index:0>2x}: {hexify(self.data)}'

        def validate_data(self):
            return

    class EntityA(Entity):
        DATA_LENGTH = 0x10

        def __repr__(self):
            details = self.details
            if details is not None:
                return '{0}  # {1}'.format(self.hexify(), self.details)
            else:
                return self.hexify()

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

                index = data['index']
                if isinstance(index, int):
                    start = index
                    finish = index + 1
                else:
                    start, finish = index
                    finish += 1
                assert finish > start
                value = int.from_bytes(self.data[start:finish],
                                       byteorder='big')
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

        def validate_data(self):
            return
            assert self.data[:2] != b'\x00\x00'
            assert self.data[1] != 0

    class EntityB(Entity):
        DATA_LENGTH = 0x14

        def validate_data(self):
            #assert self.data[0xf] & 0xf == 0
            return
            assert self.data[-4:] == b'\x00\x00\x00\x00'
            assert self.data[1] == 0

    @property
    def data_pointer(self):
        return self.reference_pointer & 0x7fffffff

    def get_decompressed(self):
        if hasattr(self, '_cached_decompressed'):
            return self._cached_decompressed
        f = get_open_file(get_outfile())
        try:
            data = decompress_from_file(f, self.data_pointer)
        except:
            data = None
        self._cached_decompressed = data
        return self.get_decompressed()

    def __repr__(self):
        header = (f'ROOM {self.index:0>3X}: {self.pointer:0>5x} -> '
                  f'{self.reference_pointer:0>8x}')
        s = header + '\n' + self.hexify()
        s = s.replace('\n', '\n  ')
        return s.strip()

    def get_entities(self):
        self.entities = []
        self.leftover_data = None
        data = self.get_decompressed()
        if data is None:
            return None

        entity_type = self.EntityA
        while True:
            if set(data) <= {0}:
                break

            if len(data) > 0xc and data[0xc] == 0x08:
                entity_type = self.EntityB

            segment_length = entity_type.DATA_LENGTH
            while len(data) < segment_length:
                data += b'\x00'
            segment, data = data[:segment_length], data[segment_length:]
            entity = entity_type(segment, self)

            if entity_type is self.EntityA and entity.is_null:
                data = segment + data
                entity_type = self.EntityB
                continue

            self.entities.append(entity)
            #if entity_type is self.EntityB and entity.is_null:
            #    break

        self.leftover_data = data
        assert set(self.leftover_data) <= {0}
        return self.entities

    def hexify(self):
        if not hasattr(self, 'entities'):
            self.get_entities()

        s = '\n'.join([str(e) for e in self.entities])
        if self.leftover_data:
            leftover = pretty_hexify(self.leftover_data).replace('\n', '\n  ')
            s = f'{s}\nLEFTOVER ({len(self.leftover_data)}):\n  {leftover}'
        return s

    def get_exit_candidates(self):
        data = self.get_decompressed()
        if data is None:
            return None
        exits = []
        while data:
            segment, data = data[:0x10], data[0x10:]
            if len(segment) < 0x10:
                break
            if segment[1] == 0x8c:
                exit_number = int.from_bytes(segment[4:6], byteorder='big')
                exits.append(exit_number)
        return exits


if __name__ == '__main__':
    try:
        print('You are using the MN64 Door Randomizer '
              'randomizer version %s.' % VERSION)

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]

        codes = {
        }

        run_interface(ALL_OBJECTS, snes=False, codes=codes,
                      custom_degree=False, custom_difficulty=False)

        #if 'export' in get_activated_codes():
        #    export_all(ALL_OBJECTS)

        for code in sorted(get_activated_codes()):
            print('Code "%s" activated.' % code)

        #MapMetaObject.get(0x40b).get_decompressed()
        '''
        for mmo in MapMetaObject.every:
            try:
                mmo.get_decompressed()
                print('PASS', hex(mmo.index), hex(mmo.data_pointer))
            except:
                print('FAIL', hex(mmo.index), hex(mmo.data_pointer))
        for mmo in MapMetaObject.every:
            data = mmo.get_decompressed()
            if data is None:
                continue
            if len(data) < 0x22:
                continue
            if data[0x21] == 0x8c:
                print(hex(mmo.index), True)
            else:
                print(hex(mmo.index), False)
        for mmo in MapMetaObject.every:
            exits = mmo.get_exit_candidates()
            if exits:
                print(hex(mmo.index), [hex(x) for x in exits])
        mmo = MapMetaObject.get(0x408)
        print(mmo)
        entities = mmo.get_entities()
        import pdb; pdb.set_trace()
        '''
        for mmo in MapMetaObject.every:
            if not (0x336 <= mmo.index <= 0x482):
                continue
            print(mmo)
            print()
        #old_pointer = 0
        #for mmo in MapMetaObject.every:
        #    if mmo.data_pointer < old_pointer:
        #        print(hex(mmo.index), hex(mmo.data_pointer))
        #    old_pointer = mmo.data_pointer
        #MapMetaObject.get(608).get_decompressed()
        #MapMetaObject.get(0x1d1).get_decompressed()

        #if 'import' in get_activated_codes():
        #    import_all(ALL_OBJECTS)

        #write_seed()

        clean_and_write(ALL_OBJECTS)
        finish_interface()

    except Exception:
        print('ERROR: %s' % format_exc())
        input('Press Enter to close this program. ')
