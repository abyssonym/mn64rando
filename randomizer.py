from randomtools.tablereader import (
    TableObject, get_global_label, addresses, names, gen_random_normal,
    get_activated_patches, mutate_normal, shuffle_normal, write_patch,
    get_random_degree, tblpath, get_open_file)
from randomtools.utils import (
    classproperty, cached_property, read_lines_nocomment,
    utilrandom as random)
from randomtools.interface import (
    get_outfile, get_seed, get_flags, get_activated_codes, activate_code,
    run_interface, rewrite_snes_meta, clean_and_write, finish_interface,
    get_sourcefile)

from collections import Counter, defaultdict
from time import time, gmtime
from io import BytesIO
from itertools import combinations
from os import path, mkdir, environ
from traceback import format_exc
import re
import yaml

from decompress_mn64 import (
    checksum, decompress_from_file, decompress, recompress)


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


class MetaSizeObject(TableObject):
    def get_metasize(self):
        return int.from_bytes(self.metasize_str, byteorder='big')

    def set_metasize(self, value):
        self.metasize_str = value.to_bytes(length=2, byteorder='big')

    def del_metasize(self):
        raise NotImplementedError

    metasize = property(get_metasize, set_metasize, del_metasize)


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
    ROM_SPLIT_THRESHOLDS = (ROM_SPLIT_THRESHOLD_LOW, ROM_SPLIT_THRESHOLD_HI)

    VIRTUAL_RAM_OFFSET = 0x212090       # Location in RAM where file 00b is
    POINTER_TABLE_OFFSET = 0x235fe8     # Pointers to room metadata

    LOADING_CODE_HEADER = (
        b'\x27\xBD\xFF\xE8\xAF\xBF\x00\x14\x3C\x04\x80\x23\x0C\x00\x4D\x95'
        b'\x24\x84')
    LOADING_CODE_FOOTER = \
        b'\x8F\xBF\x00\x14\x27\xBD\x00\x18\x03\xE0\x00\x08\x00\x00\x00\x00'

    METADATA_STRUCTURE = {
            'unknown_pointer1': (0x00, 0x04),
            'unknown_pointer2': (0x04, 0x08),
            'meta_eight1':      (0x08, 0x0a),
            'instance_offset':  (0x0a, 0x0c),
            'meta_eight2':      (0x0c, 0x0e),
            'ending_offset':    (0x0e, 0x10),
            'meta_eight3':      (0x10, 0x12),
            'footer_offset':    (0x12, 0x14),
            'file_index':       (0x14, 0x16),
            'meta_null':        (0x16, 0x18),
            'loading_pointer':  (0x18, 0x1c),
        }
    METADATA_LENGTH = 0x1c
    ENTITY_FOOTER_LENGTH = 0x1c

    MAX_WARP_INDEX = 0x1e4

    with open(ENTITY_STRUCTURES_FILENAME) as f:
        entity_structures = yaml.load(f.read(),
                                      Loader=yaml.SafeLoader)

    structure_names = set()
    for __index, __structure in entity_structures.items():
        __name = __structure['name']
        if __name in structure_names:
            raise Exception(f'Duplicate structure name: {name}')
        structure_names.add(__name)

    room_names = {}
    warp_names = {}
    for __line in read_lines_nocomment(ROOM_INDEXES_FILENAME):
        try:
            __warp_index, __data_index, __name = __line.split(' ', 2)
        except ValueError:
            __warp_index, __data_index = __line.split(' ')
            __name = None
        __warp_index = int(__warp_index, 0x10)
        __data_index = int(__data_index, 0x10)
        assert __data_index not in room_names
        assert __warp_index not in warp_names
        if __name is not None:
            room_names[__data_index] = __name
            warp_names[__warp_index] = __name

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
            return f'{parent_index}-{self.index:0>3x}'

        @property
        def details(self):
            if self.is_null:
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
                index = self.parent.instances.index(self)
                return f'+{index:0>2x}: {data}'

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

        def get_property_value(self, property_name, old=False):
            start, finish = self.get_property_indexes(property_name)
            if old:
                value = int.from_bytes(self.old_data[start:finish],
                                       byteorder='big')
            else:
                value = int.from_bytes(self.data[start:finish],
                                       byteorder='big')
            return value

        def get_pretty_value(self, property_name, old=False):
            value = self.get_property_value(property_name, old)
            if value in self.structure[property_name]:
                return self.structure[property_name][value]
            index = self.structure[property_name]['index']
            if isinstance(index, int):
                length = 1
            else:
                a, b = index
                length = (b+1) - a
            length *= 2
            return ('{0:0>%sx}' % length).format(value)

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
        def is_lock(self):
            return self.structure and 'lock_index' in self.structure

        @property
        def is_key(self):
            return self.structure and 'key_index' in self.structure

        @property
        def is_gold_dango(self):
            return self.actor_id == 0x85

        @property
        def is_silver_cat(self):
            return self.actor_id == 0x88

        @property
        def is_gold_cat(self):
            return self.actor_id == 0x89

        @property
        def is_surprise_pack(self):
            return self.actor_id == 0x91

        @property
        def is_elly_fant(self):
            return self.actor_id == 0x86

        @property
        def is_mr_arrow(self):
            return self.actor_id == 0x87

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

        @cached_property
        def definition(self):
            if self.is_null:
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
        def is_exit(self):
            if self.definition is None:
                return False
            return self.definition.is_exit

        @property
        def is_lock(self):
            if self.definition is None:
                return False
            return self.definition.is_lock

        @property
        def exit_pair(self):
            if not self.is_exit:
                return None
            coparent = MapMetaObject.get_by_warp_index(
                self.definition.get_property_value('dest_room', old=True))
            candidates = coparent.exits
            candidates = [c for c in candidates
                          if c.definition.get_property_value('dest_room',
                                                             old=True)
                          == self.parent.warp_index]
            if len(candidates) > 1:
                candidates = sorted(candidates,
                                    key=lambda c: self.compare_exit(c))
            if not candidates:
                return None
            return candidates[0]

        @property
        def lock(self):
            if not self.is_exit:
                return None
            locks = [i for i in self.parent.instances if i.is_lock]
            if not locks:
                return None
            exits = self.parent.exits
            assert self in exits
            selections = {}
            for l in locks:
                exits = sorted(exits, key=lambda x: x.get_distance(l))
                x = exits[0]
                assert x.get_distance(l) == 0
                if len(exits) > 1:
                    assert exits[1].get_distance(l) > 0
                selections[l] = x
            chosen = [l for l in locks if selections[l] is self]
            assert len(chosen) < 2
            if chosen:
                return chosen[0]
            return None

        @property
        def lock_signature(self):
            if not self.is_lock:
                return None
            key_type = self.definition.get_pretty_value('key_type').lower()
            lock_index = self.definition.get_property_value('lock_index')
            zone = self.definition.get_property_value('zone')
            return f'{zone}.{lock_index:0>3x}.{key_type}'

        def get_distance(self, other):
            assert self.parent is other.parent
            distances = []
            for pname in ['x', 'y', 'z']:
                positions = (self.get_property_value(pname),
                             other.get_property_value(pname))
                positions = [(v - 0x10000) if v & 0x8000 else v
                             for v in positions]
                diff = abs(positions[0] - positions[1])
                distances.append(diff)
            return sum(v**2 for v in distances)

        def compare_exit(self, other):
            assert self.is_exit and other.is_exit
            assert self.definition.get_property_value('dest_room', old=True) \
                    == other.parent.warp_index
            assert other.definition.get_property_value('dest_room', old=True) \
                    == self.parent.warp_index
            distances = []
            for (a, b) in [(self, other), (other, self)]:
                for pname in ['x', 'y', 'z']:
                    dname = 'dest_%s' % pname
                    positions = (a.get_property_value(pname, old=True),
                                 b.definition.get_property_value(dname,
                                                                 old=True))
                    positions = [(v - 0x10000) if v & 0x8000 else v
                                 for v in positions]
                    diff = abs(positions[0] - positions[1])
                    distances.append(diff)
            return sum(v**2 for v in distances)

        def set_main_property(self, value):
            if 'definition' in self._property_cache:
                del(self._property_cache['definition'])
            self.set_property('definition_index', value << 4)

        def acquire_destination(self, warp_index, exit_index=None):
            assert self.is_exit
            exits = []
            for mmo in MapMetaObject.sorted_rooms:
                exits += [
                    e for e in mmo.exits if warp_index ==
                    e.definition.get_property_value('dest_room', old=True)]

            if not exits:
                return

            def get_height(exit):
                height = exit.definition.get_property_value('dest_z', old=True)
                if height & 0x8000:
                    height = height - 0x10000
                return height

            if exit_index is None:
                exits = sorted(exits, key=lambda e: (get_height(e), e.index))
                chosen = exits[-1]
            else:
                mmo = MapMetaObject.get_by_warp_index(warp_index)
                exit = mmo.entities[exit_index]
                instance = [e for e in mmo.exits if e.definition is exit][0]
                chosen = instance.exit_pair
                assert isinstance(chosen, MapMetaObject.EntityInstance)
            for p in ['dest_room', 'dest_x', 'dest_y', 'dest_z',
                      'direction']:
                self.definition.set_property(
                        p, chosen.definition.get_property_value(p, old=True))

        def yeet(self):
            self.data = self.parent.instances[0].data
            assert self.definition.actor_id == 0x8e

        def validate_data(self):
            if self.is_null:
                return
            if self.definition is None:
                raise Exception(f'Instance {self.parent.warp_index:0>3x}-'
                                f'{self.definition_index:0>3x} is undefined.')
            assert self.definition.index == self.definition_index

    @classproperty
    def sorted_rooms(self):
        return sorted(
            (mmo for mmo in self.every if mmo.is_room),
            key=lambda x: x.warp_index)

    @classmethod
    def convert_loading_pointer(self, pointer):
        if isinstance(pointer, bytes):
            pointer = int.from_bytes(pointer, byteorder='big')
        if pointer >= self.VIRTUAL_RAM_OFFSET:
            pointer &= 0x7fffffff
            pointer -= self.VIRTUAL_RAM_OFFSET
            assert 0 <= pointer < self.VIRTUAL_RAM_OFFSET
            return pointer
        else:
            assert (pointer + self.VIRTUAL_RAM_OFFSET) <= 0xffffff
            return pointer + self.VIRTUAL_RAM_OFFSET

    @classmethod
    def read_loading_files(self):
        main_code = self.get(self.MAIN_CODE_INDEX)
        main_code._data = main_code.get_decompressed()
        data_start = 0xffffffff
        data_end = 0
        routine_start = 0xffffffff
        routine_end = 0
        with BytesIO(main_code._data) as f:
            for warp_index in range(self.MAX_WARP_INDEX + 1):
                base_pointer = self.convert_loading_pointer(
                        self.POINTER_TABLE_OFFSET+(warp_index*4))
                f.seek(base_pointer)
                pointer = int.from_bytes(f.read(4), byteorder='big')
                if pointer == 0:
                    continue
                f.seek(self.convert_loading_pointer(pointer))
                metadata = f.read(self.METADATA_LENGTH)
                mmo_index = int.from_bytes(metadata[0x14:0x16]) - 1
                if mmo_index < 0:
                    assert set(metadata[4:-4]) == {0}
                    continue

                mmo = MapMetaObject.get(mmo_index)
                if mmo.is_rom_split:
                    continue
                mmo.warp_index = warp_index
                max_length = 0
                for (attribute, (a, b)) in self.METADATA_STRUCTURE.items():
                    assert a < b
                    max_length = max(max_length, b)
                    value = int.from_bytes(metadata[a:b], byteorder='big')
                    setattr(mmo, attribute, value)
                assert max_length == len(metadata) == self.METADATA_LENGTH
                assert mmo.meta_eight1 == 0x800
                assert mmo.meta_eight2 == 0x800
                assert mmo.meta_eight3 == 0x800
                assert mmo.meta_null == 0
                assert mmo.file_index == mmo.index + 1
                assert mmo.ending_offset == \
                    mmo.footer_offset + self.ENTITY_FOOTER_LENGTH

                f.seek(self.convert_loading_pointer(mmo.loading_pointer))
                routine_start = min(routine_start, f.tell())
                routine = f.read(0x24)
                routine_end = max(routine_end, f.tell())
                assert routine.startswith(self.LOADING_CODE_HEADER)
                assert routine.endswith(self.LOADING_CODE_FOOTER)
                assert len(routine) == len(
                    self.LOADING_CODE_HEADER + self.LOADING_CODE_FOOTER) + 2
                offset = int.from_bytes(routine[0x12:0x14], byteorder='big')
                f.seek(self.convert_loading_pointer(0x230000 | offset))
                data_start = min(data_start, f.tell())
                warp_loads = []
                while True:
                    value = int.from_bytes(f.read(2), byteorder='big')
                    if value == 0:
                        break
                    warp_loads.append(value)
                mmo.loading_files = warp_loads
                data_end = max(data_end, f.tell())

        MapMetaObject.loading_data_start = data_start
        MapMetaObject.loading_data_end = data_end
        MapMetaObject.loading_routine_start = routine_start
        MapMetaObject.loading_routine_end = routine_end
        return

    @classmethod
    def write_loading_files(self):
        main_code = self.get(self.MAIN_CODE_INDEX)
        data_start = MapMetaObject.loading_data_start
        data_end = MapMetaObject.loading_data_end
        routine_start = MapMetaObject.loading_routine_start
        routine_end = MapMetaObject.loading_routine_end
        f = BytesIO(main_code.data)
        f.seek(data_start)
        f.write(b'\x00' * (data_end-data_start))
        f.seek(routine_start)
        f.write(b'\x00' * (routine_end-routine_start))
        data_buffer = b''
        routine_buffer = b''

        for warp_index in range(self.MAX_WARP_INDEX + 1):
            mmo = MapMetaObject.get_by_warp_index(warp_index)
            if mmo is None:
                continue
            assert not mmo.is_rom_split

            values = mmo.loading_files
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
            offset = (list_pointer & 0xffff).to_bytes(length=2,
                                                      byteorder='big')
            routine = (self.LOADING_CODE_HEADER + offset
                       + self.LOADING_CODE_FOOTER)
            if routine in routine_buffer:
                routine_offset = routine_buffer.index(routine)
            else:
                routine_offset = len(routine_buffer)
                routine_buffer += routine
            assert routine_offset % 4 == 0
            loading_pointer = self.convert_loading_pointer(routine_start +
                                                           routine_offset)
            mmo.loading_pointer = loading_pointer | 0x80000000

            mmo.instance_offset = (
                len(mmo.definitions) * mmo.EntityDefinition.DATA_LENGTH)
            mmo.footer_offset = mmo.instance_offset + (
                len(mmo.instances) * mmo.EntityInstance.DATA_LENGTH)
            mmo.ending_offset = mmo.footer_offset + self.ENTITY_FOOTER_LENGTH

            metadata_length = max(max(self.METADATA_STRUCTURE.values()))
            assert metadata_length == self.METADATA_LENGTH
            metadata = b'\x00' * metadata_length
            for (attribute, (a, b)) in self.METADATA_STRUCTURE.items():
                length = b-a
                value = getattr(mmo, attribute)
                value = value.to_bytes(length=length, byteorder='big')
                metadata = metadata[:a] + value + metadata[b:]

            base_pointer = self.convert_loading_pointer(
                    self.POINTER_TABLE_OFFSET+(warp_index*4))
            f.seek(base_pointer)
            pointer = int.from_bytes(f.read(4), byteorder='big')
            assert pointer > 0
            f.seek(self.convert_loading_pointer(pointer))
            f.write(metadata)

        try:
            assert len(data_buffer) < data_end - data_start
            assert len(routine_buffer) < routine_end - routine_start
        except AssertionError:
            print('WARNING: Loading metadata exceeds expected space.')
        f.seek(data_start)
        f.write(data_buffer)
        f.seek(routine_start)
        f.write(routine_buffer)
        f.seek(0)
        main_code._data = f.read()
        f.close()

    @classmethod
    def get_by_warp_index(self, index):
        choices = [mmo for mmo in MapMetaObject.every
                   if hasattr(mmo, 'warp_index')
                   and mmo.warp_index == index]
        if not choices:
            return None
        assert len(choices) == 1
        return choices[0]

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
                    if mmo.is_rom_split:
                        raise Exception(f'Cannot use Room {room_index:0>3x}. '
                                        f'The index is being used as a buffer '
                                        f'between old data and new data.')
                    assert mmo.entities is not None
                    mmo.entities = []
                    previous_entity = None
                    mmo.footer = b''
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
                    assert not mmo.footer
                    assert not mmo.leftover_data
                elif ':' in line:
                    previous_entity = mmo.import_line(line)
                    assert not mmo.footer
                    assert not mmo.leftover_data
                else:
                    line = [int(v, 0x10).to_bytes(length=2, byteorder='big')
                            for v in line.split()]
                    line = b''.join(line)
                    if mmo.footer:
                        mmo.leftover_data += line
                    else:
                        mmo.footer += line
                    assert len(mmo.footer) == self.ENTITY_FOOTER_LENGTH

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
        header += '\n# {0:19} {1}'.format('Total Memory Used', self.total_size)
        for attr in ('file_index', 'instance_offset', 'footer_offset',
                     'ending_offset', 'loading_pointer',
                     'unknown_pointer1', 'unknown_pointer2'):
            a, b = self.METADATA_STRUCTURE[attr]
            length = (b-a)*2
            value = ('{0:0>%sx}' % length).format(getattr(self, attr))
            header += f'\n# {attr:19} {value}'
        if self.loading_files:
            loading_files = ' '.join([f'{v:0>3x}' for v in self.loading_files])
            header += f'\n!load {loading_files}'
        s = header + '\n\n' + self.hexify()
        s = s.replace('\n', '\n  ')
        while ' \n' in s:
            s = s.replace(' \n', '\n')
        return s.strip()

    @property
    def data_pointer(self):
        if not hasattr(self, 'reference_pointer'):
            self.reference_pointer = int.from_bytes(
                self.reference_pointer_be, byteorder='big')
            self.old_data['reference_pointer'] = self.reference_pointer
        return self.reference_pointer & 0x7fffffff

    @property
    def metasize(self):
        return MetaSizeObject.get(self.index)

    @property
    def total_size(self):
        return sum([MetaSizeObject.get(index-1).metasize
                    for index in self.loading_files])

    @property
    def data(self):
        if hasattr(self, '_data'):
            return self._data
        if self.is_room:
            data = b''
            for e in self.entities:
                data += e.data
            data += self.footer
            data += self.leftover_data
            return data
        if self.index == self.MAIN_CODE_INDEX:
            assert hasattr(self, '_data')
        return None

    @property
    def data_has_changed(self):
        if self.is_rom_split:
            return False
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
        if self.is_rom_split:
            return False
        if 0x335 <= self.index <= 0x481:
            assert self.warp_index is not None
            return True
        return False

    @property
    def room_name(self):
        if self.index in self.room_names:
            return self.room_names[self.index]

    @cached_property
    def exits(self):
        return [e for e in self.instances if e.is_exit]

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
        return self.index in self.ROM_SPLIT_THRESHOLDS

    def get_compressed(self):
        if hasattr(self, '_cached_compressed'):
            return self._cached_compressed
        start = self.data_pointer
        try:
            finish = self.get(self.index+1).data_pointer
        except KeyError:
            finish = start
        if finish < start:
            assert self.is_rom_split
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
        if self.is_room:
            assert len(self._cached_decompressed) == self.metasize.metasize
        return self.get_decompressed()

    def write_decompressed_to_file(self, filename):
        with open(filename, 'w+') as f:
            pass
        with open(filename, 'r+b') as f:
            f.write(self.get_decompressed())

    def get_entities(self):
        assert not self.is_rom_split
        assert self.is_room
        if hasattr(self, 'entities'):
            return self.entities

        self.entities = []
        self.footer = None
        self.leftover_data = None
        data = self.get_decompressed()
        if data is None:
            return None

        definition_segment = data[:self.instance_offset]
        instance_segment = data[self.instance_offset:self.footer_offset]
        footer = data[self.footer_offset:self.ending_offset]
        leftover = data[self.ending_offset:]
        assert len(data) >= self.ending_offset

        while definition_segment:
            entity = self.EntityDefinition(
                definition_segment[:self.EntityDefinition.DATA_LENGTH], self)
            definition_segment = \
                definition_segment[self.EntityDefinition.DATA_LENGTH:]
            self.entities.append(entity)

        while instance_segment:
            entity = self.EntityInstance(
                instance_segment[:self.EntityInstance.DATA_LENGTH], self)
            instance_segment = \
                instance_segment[self.EntityInstance.DATA_LENGTH:]
            self.entities.append(entity)

        self.footer = footer
        self.leftover_data = leftover
        return self.entities

    def hexify(self):
        definitions = self.definitions
        instances = self.instances
        s = '# DEFINITIONS\n'
        s += '\n'.join(map(str, definitions))
        s += '\n\n# INSTANCES\n'
        s += '\n'.join(map(str, instances))
        s += '\n\n# FOOTER\n'
        s += pretty_hexify(self.footer).replace('\n', ' ') + '\n'
        if set(self.leftover_data) > {0} or True:
            s += f'\n\n# LEFTOVER ({len(self.leftover_data)})\n'
            s += pretty_hexify(self.leftover_data) + '\n'
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
        if index[0] == '+':
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
        if self.data_has_changed and self.is_room:
            old_length = self.metasize.metasize
            assert old_length == len(self._cached_decompressed)
            new_length = len(self.data)
            while new_length % 0x4:
                new_length += 1
            self.metasize.metasize = new_length
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
        if self.is_rom_split:
            data = b''
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
        try:
            assert self.entities[:len(definitions)] == definitions
            assert all(e.index == i for (i, e) in enumerate(definitions))
        except AssertionError:
            raise Exception(f'Room {self.index:0>3x}: Entity definitions must '
                             'be in order at the start.')
        for e in self.entities:
            e.validate_data()

    def preprocess(self):
        self.get_compressed()
        if self.index > 0 and not self.get(self.index-1).is_rom_split:
            assert self.data_pointer >= self.get(self.index-1).data_pointer

        if self.is_room:
            self.get_entities()
            assert not self.data_has_changed
            assert self.entities

    def preclean(self):
        if self.index >= self.MAIN_CODE_INDEX:
            self.deallocate()

    def cleanup(self):
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
    def preprocess_all(cls):
        MapMetaObject.free_space = [(addresses.free_space_start,
                                     addresses.free_space_end)]
        for mmo in MapMetaObject.every:
            mmo.warp_index = None
        cls.read_loading_files()
        super().preprocess_all()

    @classmethod
    def full_cleanup(cls):
        (a, b) = min(cls.free_space)
        if b < addresses.expected_data_end:
            print(f'WARNING: Reallocating expected available space up to '
                  f'{addresses.expected_data_end:x}.')
            cls.free_space.append((a, addresses.expected_data_end))
            cls.consolidate_free_space()
        cls.write_loading_files()  # must do this before cleaning/writing 00b
        print('Recompressing data; this may take some time.')
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
            if 'MN64_IMPORT' in environ:
                filename = environ['MN64_IMPORT']
            else:
                filename = input('Import from filename: ')
            if not filename.strip():
                filename = f'{get_sourcefile()}.import.txt'
            MapMetaObject.import_from_file(filename)
            for mmo in MapMetaObject.every:
                if mmo.is_room and mmo.data_has_changed:
                    print('Updated:', str(mmo).split('\n')[0])

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
            if 'MN64_EXPORT' in environ:
                filename = environ['MN64_EXPORT']
            else:
                filename = f'{get_outfile()}.export.txt'
            with open(filename, 'w+') as f:
                for mmo in MapMetaObject.sorted_rooms:
                    f.write(str(mmo) + '\n\n')

        #write_seed()

        clean_and_write(ALL_OBJECTS)
        checksum(get_open_file(get_outfile()))
        finish_interface()

    except Exception:
        print('ERROR: %s' % format_exc())
        input('Press Enter to close this program. ')
