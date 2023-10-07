from randomtools.tablereader import (
    TableObject, get_global_label, addresses, names, gen_random_normal,
    get_activated_patches, mutate_normal, shuffle_normal, write_patch,
    get_random_degree, tblpath, get_open_file)
from randomtools.utils import (
    classproperty, cached_property, read_lines_nocomment,
    utilrandom as random)
from randomtools.interface import (
    get_outfile, get_seed, get_flags, get_activated_codes, activate_code,
    run_interface, rewrite_snes_meta, clean_and_write, finish_interface)

from collections import Counter, defaultdict
from time import time, gmtime
from io import BytesIO
from itertools import combinations
from os import path, mkdir
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


def pretty_hexify(s, newlines=True):
    result = []
    while s:
        line, s = s[:0x10], s[0x10:]
        line_result = []
        while line:
            word, line = line[:4], line[4:]
            word = hexify(word).split(' ')
            if len(word) >= 2:
                a = f'{word[0]}{word[1]}'
            else:
                a = word[0]
            if len(word) >= 4:
                b = f'{word[2]}{word[3]}'
            elif len(word) > 2:
                b = word[2:3][0]
            else:
                b = None
            if a and b:
                word = f'{a} {b}'
            else:
                word = a
            line_result.append(word)
        result.append(' '.join(line_result))
    if newlines:
        return '\n'.join(result)
    else:
        return ' '.join(result)


class MapMetaObject(TableObject):
    ENTITY_STRUCTURES_FILENAME = path.join(tblpath, 'entity_structures.yaml')
    ROOM_INDEXES_FILENAME = path.join(tblpath, 'room_indexes.txt')

    '''
    Using extra free space is complicated.
    Pointers must ostensibly be in ascending order, because the "next" pointer
    is used to determine the size of variable length data blocks. However,
    some data, such as the MAIN_CODE_INDEX, cannot be moved. So, if we want
    to move some movable data, we have to identify breakpoints where there is
    a pointer that never gets read, so that the "next" pointer issue never
    comes up. Two such indexes are:
        336 - Room 001 - Alternate Oedo Castle Tile Room (unused)
        46d - Room 1ce - Null (unused, no exits or actors)
    '''
    MAIN_CODE_INDEX = 0xb
    ROM_SPLIT_THRESHOLD_LOW = 0x336
    ROM_SPLIT_THRESHOLD_HI = 0x46d

    MAIN_RAM_OFFSET = 0x212090
    POINTER_TABLE_OFFSET = 0x235fe8

    with open(ENTITY_STRUCTURES_FILENAME) as f:
        entity_structures = yaml.load(f.read(),
                                      Loader=yaml.SafeLoader)

    structure_names = set()
    for index, structure in entity_structures.items():
        name = structure['name']
        if name in structure_names:
            raise Exception(f'Duplicate structure name: {name}')
        structure_names.add(name)

    room_names = {}
    warp_names = {}
    warp_indexes = {}
    for line in read_lines_nocomment(ROOM_INDEXES_FILENAME):
        try:
            warp_index, data_index, name = line.split(' ', 2)
        except ValueError:
            warp_index, data_index = line.split(' ')
            name = None
        warp_index = int(warp_index, 0x10)
        data_index = int(data_index, 0x10)
        assert data_index not in warp_indexes
        assert data_index not in room_names
        assert warp_index not in warp_names
        warp_indexes[data_index] = warp_index
        if name is not None:
            room_names[data_index] = name
            warp_names[warp_index] = name

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
                for e in self.parent.entities:
                    if e.index == index:
                        raise Exception(
                            f'{self.parent.warp_index:0>3x}-{index:0>3x} '
                            f'is a duplicate entity.')
                self.index = index
            self.data = data
            self.old_data = data
            self.validate_data()

        def __repr__(self):
            details = self.details
            if details is not None:
                details = '  ' + details.replace('\n', '\n  ')
                s = '{0}\n{1}'.format(self.hexify(), details)
            else:
                s = self.hexify()
            return s

        @property
        def is_null(self):
            return set(self.data) == {0}

        @property
        def signature(self):
            parent_index = f'{self.parent.warp_index:0>3x}'
            name = self.name.strip()
            if '#' in name:
                name = name.split('#')[0].strip()
            return f'{parent_index}-{name}'

        @property
        def details(self):
            if self.is_null or self.is_footer or self.name is None:
                return None
            if not self.structure:
                return None

            unsorted_details = []
            for property_name, data in self.structure.items():
                if property_name == self.MAIN_PROPERTY_NAME:
                    continue
                if (hasattr(self, 'DETAIL_PROPERTIES') and
                        property_name not in self.DETAIL_PROPERTIES):
                    continue

                start, finish = self.get_property_indexes(property_name)
                value = self.get_property_value(property_name)
                pretty_value = ('{0:0>%sx}' % ((finish-start)*2)).format(value)
                pretty_name = f'{property_name}:'
                pretty_value = f'@ {pretty_name:15} {pretty_value}'
                if value in data:
                    pretty_value = f'{pretty_value:26}# {data[value]}'

                unsorted_details.append((start, pretty_value))
            details = [v for (s, v) in sorted(unsorted_details)]
            details.insert(0, f'@ {self.name}')
            return '\n'.join(details)

        def hexify(self):
            data = pretty_hexify(self.data, newlines=False)
            if isinstance(self, MapMetaObject.EntityDefinition):
                return f'{self.index:0>3x}: {data}'
            else:
                return f'---: {data}'

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
            if self.structure is None or property_name not in self.structure:
                raise Exception(f'Entity {self.signature} has no '
                                f'"{property_name}" property.')
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

    class EntityDefinition(EntityMixin):
        DATA_LENGTH = 0x10
        MAIN_PROPERTY_NAME = 'name'

        @property
        def actor_id(self):
            return int.from_bytes(self.data[:2], byteorder='big')

        @property
        def name(self):
            if self.structure is None:
                return f'{self.actor_id:0>3x}'
            actor_id = f'{self.actor_id:0>3x}'
            result = f'{actor_id:24}# {self.structure["name"]}'
            if self.comment:
                result = f'{result} {self.comment}'
            return result

        @property
        def structure(self):
            if self.actor_id not in MapMetaObject.entity_structures:
                return None
            return MapMetaObject.entity_structures[self.actor_id]

        @property
        def is_exit(self):
            return self.structure and 'dest_room' in self.structure

        @property
        def comment(self):
            if self.is_exit:
                if self.get_property_value('misc') == 0:
                    return '(no destination)'
                dest_room = self.get_property_value('dest_room')
                if dest_room in MapMetaObject.warp_names:
                    dest_name = MapMetaObject.warp_names[dest_room]
                    return f'to {dest_room:0>3x}: {dest_name}'
                else:
                    parent_index = self.parent.warp_index
                    return (f'to unknown: {parent_index:0>3x} '
                            f'-> {dest_room:0>3x}')

        @property
        def is_footer(self):
            return False

        def set_main_property(self, value):
            actor_id = value.to_bytes(length=2, byteorder='big')
            data = actor_id + self.data[2:]
            assert len(data) == len(self.data)
            self.data = data
            assert self.actor_id == value

    class EntityInstance(EntityMixin):
        DATA_LENGTH = 0x14
        MAIN_PROPERTY_NAME = 'definition_index'
        DETAIL_PROPERTIES = ['x', 'y', 'z']

        structure = {'definition_index':    {'index': (0xe, 0xf)},
                     'x':                   {'index': (0x0, 0x1)},
                     'z':                   {'index': (0x2, 0x3)},
                     'y':                   {'index': (0x4, 0x5)},
                     }

        @property
        def definition_index(self):
            definition_index = self.get_property_value('definition_index')
            if definition_index & 0xf == 0:
                return definition_index >> 4
            return None

        @property
        def name(self):
            if self.definition_index is None:
                return None
            assert self.definition_index <= 0xfff
            comment = self.comment
            if comment:
                comment = comment.replace('@', '')
                comment = comment.replace('#', '')
                comment = comment.replace('\n', ' ')
                while '  ' in comment:
                    comment = comment.replace('  ', ' ').strip()
                return f'{self.definition_index:0>3x}  # {comment}'
            return f'{self.definition_index:0>3x}'

        @property
        def definition(self):
            if self.is_null or self.is_footer:
                return None
            if self in self.parent.entities[-2:]:
                return None
            if self.definition_index is None:
                return None
            if self.definition_index >= len(self.parent.entities):
                return None
            definition = self.parent.entities[self.definition_index]
            if isinstance(definition, MapMetaObject.EntityDefinition):
                return definition
            return None

        @property
        def comment(self):
            if not self.definition:
                return
            if not self.definition.name:
                return f'{self.definition.actor_id:0>3x}'
            return self.definition.name

        @property
        def is_footer(self):
            if len(self.parent.entities) < 3:
                return True
            if (self in self.parent.entities[-2:]
                    and self.parent.entities[-3].is_null):
                return True
            return False

        @property
        def is_exit(self):
            if self.definition is None:
                return False
            return self.definition.is_exit

        def set_main_property(self, value):
            self.set_property('definition_index', value << 4)

        def acquire_destination(self, warp_index):
            assert self.is_exit
            for mmo in MapMetaObject.sorted_rooms:
                for e in mmo.instances:
                    if not e.is_exit:
                        continue
                    if not e.definition.get_property_value('dest_room') \
                            == warp_index:
                        continue
                    for p in ['dest_room', 'dest_x', 'dest_y', 'dest_z',
                              'direction']:
                        self.definition.set_property(
                                p, e.definition.get_property_value(p))
                    break
                else:
                    continue
                break

        def yeet(self):
            self.data = self.parent.instances[0].data
            assert self.definition.actor_id == 0x8e

    @classproperty
    def sorted_rooms(self):
        return sorted(
            (mmo for mmo in self.every if mmo.warp_index is not None),
            key=lambda x: x.warp_index)

    @classmethod
    def convert_loading_pointer(self, pointer):
        if isinstance(pointer, bytes):
            pointer = int.from_bytes(pointer, byteorder='big')
        if pointer >= self.MAIN_RAM_OFFSET:
            pointer &= 0x7fffffff
            pointer -= self.MAIN_RAM_OFFSET
            assert pointer < self.MAIN_RAM_OFFSET
            return pointer
        else:
            return pointer + self.MAIN_RAM_OFFSET

    @classmethod
    def read_loading_files(self):
        main_code = self.get(self.MAIN_CODE_INDEX)
        main_code._data = main_code.get_decompressed()
        loading_files = {}
        loading_file_pointers = {}
        data_start = 0xffffffff
        data_end = 0
        with BytesIO(main_code._data) as f:
            for warp_index in range(0x1e5):
                loading_files[warp_index] = []
                base_pointer = self.convert_loading_pointer(
                        self.POINTER_TABLE_OFFSET+(warp_index*4))
                f.seek(base_pointer)
                pointer = int.from_bytes(f.read(4), byteorder='big')
                if pointer == 0:
                    continue
                assert (pointer & 0x7fffffff) > self.MAIN_RAM_OFFSET
                f.seek(self.convert_loading_pointer(pointer) + 0x18)
                f.seek(self.convert_loading_pointer(f.read(4)) + 0x12)
                assert warp_index not in loading_file_pointers
                loading_file_pointers[warp_index] = f.tell()
                offset = int.from_bytes(f.read(2), byteorder='big')
                f.seek(self.convert_loading_pointer(0x230000 | offset))
                data_start = min(data_start, f.tell())
                warp_loads = []
                while True:
                    value = int.from_bytes(f.read(2), byteorder='big')
                    if value == 0:
                        break
                    value = value - 1
                    warp_loads.append(value)
                data_end = max(data_end, f.tell())
                loading_files[warp_index] = warp_loads

        MapMetaObject._loading_files = loading_files
        MapMetaObject.loading_file_pointers = loading_file_pointers
        MapMetaObject.loading_data_start = data_start
        MapMetaObject.loading_data_end = data_end

    @classmethod
    def write_loading_files(self):
        main_code = self.get(self.MAIN_CODE_INDEX)
        sorted_indexes = sorted(
            self._loading_files,
            key=lambda k: (-len(self._loading_files[k]), k))
        data_start = MapMetaObject.loading_data_start
        data_end = MapMetaObject.loading_data_end
        f = BytesIO(main_code.data)
        f.seek(data_start)
        f.write(b'\x00' * (data_end-data_start))
        data_buffer = b''
        for warp_index in sorted_indexes:
            if warp_index not in MapMetaObject.loading_file_pointers:
                continue
            values = MapMetaObject._loading_files[warp_index]
            values = [v+1 for v in values]
            data_list = b''.join([v.to_bytes(length=2, byteorder='big')
                                  for v in values])
            data_list += b'\x00\x00'
            for i in range(len(data_buffer)//4):
                index = i*4
                if data_buffer[index:index+len(data_list)] == data_list:
                    break
            else:
                while len(data_buffer) % 4:
                    data_buffer += b'\x00'
                index = len(data_buffer)
                data_buffer += data_list
            assert index % 4 == 0
            list_pointer = self.convert_loading_pointer(data_start+index)
            pointer_pointer = MapMetaObject.loading_file_pointers[warp_index]
            f.seek(pointer_pointer)
            f.write((list_pointer & 0xffff).to_bytes(length=2,
                                                     byteorder='big'))
        assert len(data_buffer) < data_end - data_start
        f.seek(data_start)
        f.write(data_buffer)
        f.seek(0)
        main_code._data = f.read()
        f.close()

    @classmethod
    def get_by_warp_index(self, index):
        return [mmo for mmo in MapMetaObject.every
                if mmo.warp_index == index][0]

    @classmethod
    def import_from_file(self, filename):
        mmo = None
        previous_entity = None
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
                    mmo = MapMetaObject.get_by_warp_index(room_index)
                    assert mmo.entities is not None
                    mmo.entities = []
                    previous_entity = None
                    mmo.leftover_data = b''
                elif line.startswith('LEFTOVER'):
                    previous_entity = None
                    mmo.leftover_data = b''
                elif line.startswith('!load '):
                    line = line[6:]
                    values = [int(v, 0x10) for v in line.split()]
                    mmo.loading_files = values
                elif line.startswith('@'):
                    line = line.replace(' ', '')
                    line = line[1:]
                    assert '@' not in line
                    if ':' in line:
                        property_name, value = line.split(':')
                        previous_entity.set_property(property_name,
                                                     int(value, 0x10))
                    else:
                        previous_entity.set_main_property(int(line, 0x10))
                elif ':' in line:
                    previous_entity = mmo.import_line(line)
                else:
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

    def __repr__(self):
        if self.warp_index is not None:
            header = f'ROOM {self.warp_index:0>3X}: '
        else:
            header = f'ROOM: '
        header += (f'{self.index:0>3x},{self.pointer:0>5x}->'
                   f'{self.reference_pointer:0>8x}')
        if self.room_name:
            header += f'  # {self.room_name}'
        if self.loading_files:
            loading_files = ' '.join([f'{v:0>3x}' for v in self.loading_files])
            header += f'\n!load {loading_files}'
        s = header + '\n' + self.hexify()
        s = s.replace('\n', '\n  ')
        return s.strip()

    @property
    def data_pointer(self):
        if not hasattr(self, 'reference_pointer'):
            self.reference_pointer = int.from_bytes(
                self.reference_pointer_be, byteorder='big')
            self.old_data['reference_pointer'] = self.reference_pointer
        return self.reference_pointer & 0x7fffffff

    @property
    def data(self):
        if hasattr(self, '_data'):
            if self.is_room:
                assert self.is_rom_split
            return self._data
        if self.is_room:
            data = b''
            for e in self.entities:
                data += e.data
            if self.leftover_data is not None:
                data += self.leftover_data
            return data
        if self.index == self.MAIN_CODE_INDEX:
            assert hasattr(self, '_data')
        return None

    @property
    def data_has_changed(self):
        if self.data is None:
            return False
        old_data = self._cached_decompressed
        data = self.data
        while len(data) < len(old_data):
            data += b'\x00'
        while len(old_data) < len(data):
            old_data += b'\x00'
        return data != old_data

    @property
    def is_room(self):
        if 0x335 <= self.index <= 0x481:
            assert self.warp_index is not None
            return True
        return False

    @property
    def warp_index(self):
        if self.index in self.warp_indexes:
            return self.warp_indexes[self.index]

    @property
    def room_name(self):
        if self.index in self.room_names:
            return self.room_names[self.index]

    def get_loading_files(self):
        if self.warp_index in self._loading_files:
            return self._loading_files[self.warp_index]

    def set_loading_files(self, loading_files):
        self._loading_files[self.warp_index] = loading_files

    def del_loading_files(self):
        self._loading_files[self.warp_index] = []

    loading_files = property(get_loading_files, set_loading_files,
                             del_loading_files)

    @property
    def definitions(self):
        self.get_entities()
        return [e for e in self.entities
                if isinstance(e, self.EntityDefinition)]

    @property
    def instances(self):
        self.get_entities()
        return [e for e in self.entities
                if isinstance(e, self.EntityInstance)]

    @property
    def is_compressed(self):
        return bool(self.reference_pointer & 0x80000000)

    @property
    def is_old_rom(self):
        return not self.is_new_rom

    @property
    def is_new_rom(self):
        return self.ROM_SPLIT_THRESHOLD_LOW < self.index <= \
                self.ROM_SPLIT_THRESHOLD_HI

    @property
    def is_rom_split(self):
        return self.index in (self.ROM_SPLIT_THRESHOLD_LOW,
                              self.ROM_SPLIT_THRESHOLD_HI)

    def get_compressed(self):
        if hasattr(self, '_cached_compressed'):
            return self._cached_compressed
        start = self.data_pointer
        try:
            finish = self.get(self.index+1).data_pointer
        except KeyError:
            finish = start
        f = get_open_file(get_outfile())
        f.seek(start)
        self._cached_compressed = f.read(finish-start)
        self._deallocation_start = start
        self._deallocation_finish = finish
        return self.get_compressed()

    def get_decompressed(self):
        if hasattr(self, '_cached_decompressed'):
            return self._cached_decompressed
        start = self.data_pointer
        if self.is_compressed:
            f = get_open_file(get_outfile())
            data = decompress_from_file(f, start)
        else:
            data = self.get_compressed()
        self._cached_decompressed = data
        return self.get_decompressed()

    def write_decompressed_to_file(self, filename):
        with open(filename, 'w+') as f:
            pass
        with open(filename, 'r+b') as f:
            f.write(self.get_decompressed())

    def get_entities(self):
        assert self.is_room

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

        self.leftover_data = data
        assert set(self.leftover_data) <= {0}
        self.definition_limit = len(self.definitions)
        return self.entities

    def hexify(self):
        definitions = self.definitions
        instances = self.instances
        s = '# DEFINITIONS\n'
        s += '\n'.join(map(str, definitions))
        s += '\n\n# INSTANCES\n'
        s += '\n'.join(map(str, instances))
        s += '\n\n'
        if self.leftover_data:
            leftover = pretty_hexify(self.leftover_data).replace('\n', '\n  ')
            s = f'{s}\nLEFTOVER ({len(self.leftover_data)}):\n  {leftover}'
        while '\n\n\n' in s:
            s = s.replace('\n\n\n', '\n\n')
        return s.strip()

    def import_line(self, line):
        if '#' in line:
            line = line.split('#')[0]
        assert '@' not in line

        line = line.strip()
        if not line:
            return

        assert ':' in line
        line = line.replace(' ', '').strip()
        index, line = line.split(':')
        if set(index) == {'-'}:
            index = None
        else:
            index = int(index, 0x10)

        new_data = []
        while line:
            new_data.append(int(line[:2], 0x10))
            line = line[2:]
        new_data = bytes(new_data)

        for entity_type in (self.EntityDefinition,
                            self.EntityInstance):
            if len(new_data) == entity_type.DATA_LENGTH:
                break
        else:
            raise Exception('Improper import data length.')

        new_entity = entity_type(new_data, self, index)
        self.entities.append(new_entity)
        self.entities = sorted(self.entities, key=lambda e: e.index)
        return new_entity

    def deallocate(self):
        start = self._deallocation_start
        finish = self._deallocation_finish
        for mmo in MapMetaObject.every:
            if start < mmo.data_pointer < finish:
                finish = mmo.data_pointer
        if finish <= start:
            return
        MapMetaObject.free_space.append((start, finish))
        self.consolidate_free_space()

    def allocate(self, length):
        for (a, b) in sorted(MapMetaObject.free_space):
            if a < addresses.free_space_start and self.is_new_rom:
                continue
            elif a >= addresses.free_space_start and self.is_old_rom:
                continue
            if b-a >= length:
                break
        else:
            raise Exception('No free space.')
        start, finish = a, b
        MapMetaObject.free_space.remove((start, finish))
        new_start = start+length
        if length != 0:
            assert start < new_start <= finish
        if new_start <= finish:
            MapMetaObject.free_space.append((new_start, finish))
            MapMetaObject.free_space = sorted(MapMetaObject.free_space)
        if self.is_new_rom:
            assert start >= addresses.free_space_start
        return start

    def compress_and_write(self):
        if self.data_has_changed and self.is_compressed:
            data = recompress(self.data)
        elif self.data_has_changed:
            data = self.data
        elif self.is_compressed:
            data = self.get_compressed()
        else:
            data = self.get_decompressed()
        data += b'\x00\x00\x00\x00'
        while len(data) % 0x10:
            data += b'\x00'
        address = self.allocate(len(data))
        f = get_open_file(get_outfile())
        f.seek(address)
        f.write(data)
        new_pointer = (self.reference_pointer & 0x80000000) | address
        self.reference_pointer = new_pointer
        self.relocated = True

    def validate_entities(self):
        assert self.is_room
        definitions = self.definitions
        if len(definitions) > self.definition_limit:
            raise Exception(f'Room {self.warp_index:0>3x}: Number of entity '
                            f'types must equal {self.definition_limit}.')
        try:
            assert self.entities[:len(definitions)] == definitions
            assert all(e.index == i for (i, e) in enumerate(definitions))
        except AssertionError:
            raise Exception(f'Room {self.index:0>3x}: Entity definitions must '
                             'be in order at the start.')

    def preprocess(self):
        if not hasattr(MapMetaObject, 'free_space'):
            MapMetaObject.free_space = [(addresses.free_space_start,
                                         addresses.free_space_end)]

        self.get_compressed()
        if self.index > 0:
            assert self.data_pointer >= self.get(self.index-1).data_pointer

        if self.is_room:
            self.get_entities()
            assert not self.data_has_changed
            assert self.entities

        if self.index == self.MAIN_CODE_INDEX:
            self.read_loading_files()

    def preclean(self):
        if self.index >= self.MAIN_CODE_INDEX:
            self.deallocate()

    def cleanup(self):
        if self.is_rom_split:
            if self.data_has_changed:
                raise Exception(f'Cannot use file {self.index:0>3x}. '
                                f'This index is being used as a buffer '
                                f'between old data and new data.')
            self._data = b'\x00\x00\x00\x00'
        if self.is_room and self.data_has_changed:
            self.validate_entities()
        if self.index >= self.MAIN_CODE_INDEX:
            self.compress_and_write()
            # for whatever reason, pointers must be in ascending order
            assert self.relocated
            try:
                assert not hasattr(self.get(self.index+1), 'relocated')
            except KeyError:
                pass
            if self.index > 0:
                previous = self.get(self.index-1)
                if not (self.is_rom_split or previous.is_rom_split):
                    if hasattr(previous, 'relocated'):
                        if self.is_room == previous.is_room:
                            assert previous.reference_pointer & 0x7fffffff \
                                    <= self.reference_pointer & 0x7fffffff
        if self.is_new_rom:
            assert self.data_pointer >= addresses.free_space_start
        elif self.is_old_rom:
            assert self.data_pointer < addresses.free_space_start
        assert self.old_data['reference_pointer'] & 0x80000000 == \
                self.reference_pointer & 0x80000000
        self.reference_pointer_be = self.reference_pointer.to_bytes(
            length=4, byteorder='big')
        if self.index <= self.MAIN_CODE_INDEX:
            assert self.reference_pointer_be == \
                    self.old_data['reference_pointer_be']

    @classmethod
    def full_cleanup(cls):
        print('Recompressing data; this may take some time.')
        cls.write_loading_files()
        super().full_cleanup()
        # for whatever reason, pointers must be in ascending order
        reference_pointers = [mmo.reference_pointer & 0x7fffffff for
                              mmo in cls.every if mmo.is_old_rom]
        assert reference_pointers == sorted(reference_pointers)
        reference_pointers = [mmo.reference_pointer & 0x7fffffff for
                              mmo in cls.every if not mmo.is_new_rom]
        assert reference_pointers == sorted(reference_pointers)
        for prev_mmo in cls.every:
            if prev_mmo.is_rom_split:
                continue
            try:
                next_mmo = cls.get(prev_mmo.index+1)
            except KeyError:
                continue
            assert 0 <= next_mmo.data_pointer-prev_mmo.data_pointer <= 0x7ffff


if __name__ == '__main__':
    try:
        print('You are using the MN64 Door Randomizer '
              'randomizer version %s.' % VERSION)

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]

        codes = {
            'export': ['export'],
            'import': ['import'],
        }

        run_interface(ALL_OBJECTS, snes=False, n64=True, codes=codes,
                      custom_degree=False, custom_difficulty=False)

        for code in sorted(get_activated_codes()):
            print('Code "%s" activated.' % code)

        if 'import' in get_activated_codes():
            print('IMPORTING')
            MapMetaObject.import_from_file('to_import.txt')
            for mmo in MapMetaObject.every:
                if mmo.is_room and mmo.data_has_changed:
                    print(mmo)

        if 'export' in get_activated_codes():
            print('EXPORTING')
            if DEBUG_MODE:
                try:
                    mkdir('export')
                except FileExistsError:
                    pass
                for mmo in MapMetaObject.every:
                    filename = f'{mmo.index:0>3x}.bin'
                    mmo.write_decompressed_to_file(path.join('export',
                                                             filename))
            with open('to_import.txt', 'w+') as f:
                for mmo in MapMetaObject.sorted_rooms:
                    f.write(str(mmo) + '\n\n')

        #write_seed()

        clean_and_write(ALL_OBJECTS)
        finish_interface()

    except Exception:
        print('ERROR: %s' % format_exc())
        input('Press Enter to close this program. ')
