from randomtools.tablereader import (
    TableObject, get_global_label, addresses, names, gen_random_normal,
    get_activated_patches, mutate_normal, shuffle_normal, write_patch,
    get_random_degree, tblpath, get_open_file)
from randomtools.utils import (
    classproperty, cached_property, clached_property, read_lines_nocomment,
    utilrandom as random)
from randomtools.interface import (
    get_outfile, get_seed, get_flags, get_activated_codes, activate_code,
    run_interface, rewrite_snes_meta, clean_and_write, finish_interface,
    get_sourcefile)

from collections import Counter, defaultdict
from datetime import datetime
from functools import lru_cache, total_ordering
from io import BytesIO
from itertools import product
from os import path, mkdir, environ
from time import time, gmtime
from traceback import format_exc

import re
from randomtools.utils import fake_yaml as yaml

from decompress_mn64 import (
    checksum, decompress_from_file, decompress, recompress)


VERSION = "1.2"
ALL_OBJECTS = None
DEBUG_MODE = False
VERBOSE = False


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


def consolidate_free_space(free_space):
    while True:
        updated = False
        for (a1, b1) in sorted(free_space):
            if updated:
                break
            for (a2, b2) in sorted(free_space):
                if updated:
                    break
                if (a1, b1) == (a2, b2):
                    continue
                if a2 < a1:
                    continue
                if a1 <= a2 <= b1:
                    free_space.remove((a1, b1))
                    free_space.remove((a2, b2))
                    free_space.add((a1, max(b1, b2)))
                    updated = True
        if not updated:
            break
    return free_space


class ConvertPointerMixin:
    @classmethod
    def convert_pointer(self, pointer):
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


class MetaSizeObject(TableObject):
    def get_metasize(self):
        return int.from_bytes(self.metasize_str, byteorder='big')

    def set_metasize(self, value):
        self.metasize_str = value.to_bytes(length=3, byteorder='big')

    def del_metasize(self):
        raise NotImplementedError

    metasize = property(get_metasize, set_metasize, del_metasize)

    @property
    def effective_metasize(self):
        if self.metasize % 0x40 == 0:
            return self.metasize
        m = self.metasize + (0x40-(self.metasize % 0x40))
        assert m % 0x40 == 0
        return m


class MapMetaObject(TableObject, ConvertPointerMixin):
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
        46d - Room 1ce - Unknown Training Gym (unused, no exits or actors)
        482 - Room 1e3 - Unknown (goes to credits sequence, unused?)
    '''
    MAIN_CODE_INDEX = 0xb
    MAX_WARP_INDEX = 0x1e3
    FORCE_OLD_POINTER = (list(range(0x335)) +
                         list(range(0x482, 0x520)))

    ROM_SPLIT_THRESHOLD_LOW = 0x336
    ROM_SPLIT_THRESHOLD_HI = 0x46d
    ROM_SPLIT_THRESHOLDS = (ROM_SPLIT_THRESHOLD_LOW, ROM_SPLIT_THRESHOLD_HI)

    LOADING_CODE_HEADER = \
        b'\x27\xBD\xFF\xE8\xAF\xBF\x00\x14\x3C\x04\x80\x23\x0C\x00'
    LOADING_CODE_FOOTER = \
        b'\x8F\xBF\x00\x14\x27\xBD\x00\x18\x03\xE0\x00\x08\x00\x00\x00\x00'

    BGM_GROUPS = {
        (0x1a, 0x1b),
        (0x40, 0x41, 0x42),
        (0x59, 0x5a, 0x5b),
        (0x54, 0x55, 0x53),
        }

    DEBUG_WARP_CATEGORIES = {
        0x000:  'SIRO',
        0x12c:  'DOUCHU',
        0x15e:  'MACHI',
        0x190:  'SHOP',
        }

    MUSASHI_IGA_TUNNEL = 0x131

    METADATA_STRUCTURE = {
            'persist_actor_ptr':    (0x00, 0x04),
            'event_source_ptr':     (0x04, 0x08),
            'meta_eight1':          (0x08, 0x0a),
            'instance_offset':      (0x0a, 0x0c),
            'meta_eight2':          (0x0c, 0x0e),
            'ending_offset':        (0x0e, 0x10),
            'meta_eight3':          (0x10, 0x12),
            'footer_offset':        (0x12, 0x14),
            'file_index':           (0x14, 0x16),
            'meta_null':            (0x16, 0x18),
            'loading_pointer':      (0x18, 0x1c),
        }
    METADATA_LENGTH = 0x1c
    ENTITY_FOOTER_LENGTH = 0x1c

    ENTITY_FILES = {}
    EXTRA_DEPENDENCIES = {
            0x1b6: {0x20},
            0x354: {0x20},
            0x3ef: {0x27},
        }

    NO_ENEMY_RANDOMIZE = [0x39, 0x3b, 0x40]

    with open(ENTITY_STRUCTURES_FILENAME) as f:
        ENTITY_STRUCTURES = yaml.safe_load(f.read())

    structure_names = set()
    for __index, __structure in ENTITY_STRUCTURES.items():
        __name = __structure['name']
        if __name in structure_names:
            raise Exception(f'Duplicate structure name: {name}')
        structure_names.add(__name)

    MINIMUM_SAFE_BUDGET = 0xb0000
    ENEMY_FILES = {0x20, 0x21, 0x23, 0x24, 0x25, 0x26, 0x27}
    PICKUP_FILES = {0x1a, 0x1c, 0x2b}

    JP_EN_NODE_MAPPING = {
        '13b-00e': '13b-00c',
        '152-014': '152-010',
        '16b-00a': '16b-00b',
        }
    EN_JP_NODE_MAPPING = {v: k for (k, v) in JP_EN_NODE_MAPPING.items()}

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

    INITIAL_FREE_MEMORY_FLAGS = frozenset(range(0x140, 0x158))

    available_memory_flags = set(INITIAL_FREE_MEMORY_FLAGS)
    entity_signatures = {}

    class EntityMixin:
        DICT_MATCHER = re.compile('{[^}]*}')

        def __init__(self, data, parent, index=None, validate=True):
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
            if validate:
                self.validate_data()
            self.signature

        def __repr__(self):
            data = pretty_hexify(self.data, newlines=False)
            if isinstance(self, MapMetaObject.EntityDefinition):
                hexified = f'{self.index:0>3x}: {data}'
            else:
                for index, i in enumerate(self.parent.instances):
                    if self is i:
                        break
                else:
                    index = -1
                hexified = f'+{index:0>2x}: {data}'

            details = self.details
            if details is not None:
                details = '  ' + details.replace('\n', '\n  ')
                s = '{0}\n{1}'.format(hexified, details)
            else:
                s = hexified
            return s

        @property
        def is_null(self):
            return set(self.data) == {0}

        @property
        def signature(self):
            if self in MapMetaObject.entity_signatures:
                return MapMetaObject.entity_signatures[self]
            parent_index = f'{self.parent.warp_index:0>3x}'
            name = self.name.strip()
            if '#' in name:
                name = name.split('#')[0].strip()
            signature = f'{parent_index}-{self.index:0>3x}'
            if signature in MapMetaObject.entity_signatures:
                counter = 2
                while True:
                    test = f'{signature}-{counter}'
                    if test not in MapMetaObject.entity_signatures:
                        break
                    counter += 1
                signature = test
            MapMetaObject.entity_signatures[signature] = self
            MapMetaObject.entity_signatures[self] = signature
            return self.signature


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

        def validate_data(self):
            return

        def get_property_indexes(self, property_name, old=False):
            if old:
                data = self.old_structure[property_name]
            else:
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
            if old:
                start, finish = self.get_property_indexes(property_name,
                                                          old=True)
                value = int.from_bytes(self.old_data[start:finish],
                                       byteorder='big')
            else:
                start, finish = self.get_property_indexes(property_name)
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
                for i, name in self.structure[property_name].items():
                    if name == value:
                        value = i
                        break
                else:
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

    @total_ordering
    class EntityDefinition(EntityMixin):
        DATA_LENGTH = 0x10
        MAIN_PROPERTY_NAME = 'name'

        DOOR_DESIGNS = {
            0x23a: set(),
            0x23b: set(),
            0x23c: {0},
            0x23d: set(),
            0x23f: {6, 7},
            0x240: set(),
            0x241: {5},
            0x242: {5},
            0x24d: set(),
            0x256: set(),
            0x31f: {3},
            0x321: {1, 2},
            0x32f: {4, 8},
            0x340: set(),
            0x34b: set(),
            0x3c8: set(),
            }

        def __hash__(self):
            return id(self)

        def __eq__(self, other):
            return self is other

        def __lt__(self, other):
            return self.signature < other.signature

        @property
        def actor_id(self):
            return int.from_bytes(self.data[:2], byteorder='big')

        @property
        def old_actor_id(self):
            return int.from_bytes(self.old_data[:2], byteorder='big')

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
            if self.actor_id not in MapMetaObject.ENTITY_STRUCTURES:
                return None
            return MapMetaObject.ENTITY_STRUCTURES[self.actor_id]

        @cached_property
        def old_structure(self):
            if self.old_actor_id not in MapMetaObject.ENTITY_STRUCTURES:
                return None
            return MapMetaObject.ENTITY_STRUCTURES[self.old_actor_id]

        @property
        def instances(self):
            return [i for i in self.parent.instances if i.definition is self]

        @property
        def is_exit(self):
            return (self.structure and 'dest_room' in self.structure
                    and self.get_property_value('misc_exit_id') != 0)

        @property
        def is_door(self):
            return (self.structure and 'exit_id' in self.structure
                    and not self.is_exit)

        @property
        def exit_id(self):
            if self.is_exit:
                return self.get_property_value('misc_exit_id') & 0xf
            elif self.is_door:
                return self.get_property_value('exit_id')

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
        def is_cat(self):
            return self.is_silver_cat or self.is_gold_cat

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
        def is_battery(self):
            return self.actor_id in {0x32d, 0x3c7}

        @property
        def is_pot(self):
            return self.actor_id == 0x192

        @property
        def is_pickup(self):
            return (self.is_key or self.is_gold_dango or self.is_silver_cat or
                    self.is_gold_cat or self.is_surprise_pack or
                    self.is_elly_fant or self.is_mr_arrow)

        @property
        def is_enemy(self):
            return MapMetaObject.ENTITY_FILES[self.actor_id] in \
                    MapMetaObject.ENEMY_FILES

        @property
        def door(self):
            assert self.is_exit
            candidates = [d for d in self.parent.definitions
                          if d.is_door and d.exit_id == self.exit_id]
            assert len(candidates) <= 1
            if candidates:
                return candidates[0]
            return None

        @property
        def exit(self):
            assert self.is_door
            candidates = [x for x in self.parent.definitions
                          if x.is_exit and x.exit_id == self.exit_id]
            assert len(candidates) == 1
            return candidates[0]

        @property
        def destination_parent(self):
            assert self.is_exit
            return MapMetaObject.get_by_warp_index(
                    self.get_property_value('dest_room'))

        @cached_property
        def destination_has_same_bgm(self):
            assert self.is_exit
            return self.parent.matches_bgm(self.destination_parent)

        @property
        def comment(self):
            if self.is_exit:
                dest_room = self.get_property_value('dest_room')
                if dest_room in MapMetaObject.warp_names:
                    dest_name = MapMetaObject.warp_names[dest_room]
                    return f'to {dest_room:0>3x}: {dest_name}'
                else:
                    parent_index = self.parent.warp_index
                    return (f'to unknown: {parent_index:0>3x} '
                            f'-> {dest_room:0>3x}')

        def remove(self):
            associations = [(d, d.instances) for d in self.parent.definitions]
            for group, instances in self.parent.spawn_groups.items():
                self.parent.spawn_groups[group] = [i for i in instances
                                                   if i not in self.instances]
            self.parent.definitions.remove(self)
            for n, definition in enumerate(self.parent.definitions):
                definition.index = n
                for (d, instances) in associations:
                    if d is definition:
                        for i in instances:
                            i.set_main_property(definition.index)
            assert self not in self.parent.entities
            for i in self.instances:
                assert i not in self.parent.entities

        def set_main_property(self, value):
            actor_id = value.to_bytes(length=2, byteorder='big')
            data = actor_id + self.data[2:]
            assert len(data) == len(self.data)
            self.data = data
            assert self.actor_id == value

        def set_exit_id(self, exit_id):
            assert self.is_exit or self.is_door
            if self.is_exit:
                assert not exit_id & 0xf0
                value = self.get_property_value('misc_exit_id') & 0xf0
                self.set_property('misc_exit_id', value | exit_id)
            elif self.is_door:
                self.set_property('exit_id', exit_id)

        def become_regular_door(self):
            if self.is_door and not self.is_lock:
                return
            assert self.is_lock
            designs = sorted({k for k in self.DOOR_DESIGNS
                              if self.get_property_value('door_design')
                              in self.DOOR_DESIGNS[k]})
            if len(designs) == 1:
                design = designs[0]
            else:
                temp = {e.actor_id for e in self.parent.definitions
                        if e.is_door and e is not self}
                temp = sorted(temp & set(designs))
                if temp:
                    designs = temp
                design = random.choice(designs)
            x = self.exit
            lock_index = self.get_property_value('lock_index')
            self.parent.free_memory_flag(lock_index)
            self.data = b'\x00' * len(self.data)
            self.set_main_property(design)
            self.set_exit_id(x.exit_id)

        def become_locked_door(self, key):
            LOCK_INDEX = 0x23e
            assert self.actor_id in self.DOOR_DESIGNS
            options = self.DOOR_DESIGNS[self.actor_id]
            temp = {e.get_property_value('door_design', old=True)
                    for e in self.parent.definitions
                    if e.old_structure and 'door_design' in e.old_structure}
            temp = temp & options
            if temp:
                options = temp
            door_design = random.choice(sorted(options))
            exit_id = self.get_property_value('exit_id')
            self.data = b'\x00' * len(self.data)
            self.set_main_property(LOCK_INDEX)
            self.set_property('door_design', door_design)
            self.set_property('key_type', key.get_pretty_value('key_type'))
            self.set_property('lock_index', self.parent.acquire_memory_flag())
            self.set_property('accept_key',
                              key.get_property_value('key_index'))
            self.set_property('exit_id', exit_id)

        def become_key(self, key_type):
            KEY_INDEX = 0x193
            if 'enemies' in self.old_structure:
                enemies = self.get_property_value('enemies', old=True)
            else:
                enemies = 0
            self.data = b'\x00' * len(self.data)
            self.set_main_property(KEY_INDEX)
            self.set_property('key_type', key_type)
            self.set_property('key_index', self.parent.acquire_memory_flag())
            self.set_property('enemies', enemies)

        def become_gold_dango(self):
            GOLD_DANGO_INDEX = 0x85
            if self.is_key:
                key_index = self.get_property_value('key_index')
                self.parent.free_memory_flag(key_index)
            elif 'flag' in self.structure:
                self.parent.free_memory_flag(self.get_property_value('flag'))
            self.data = b'\x00' * len(self.data)
            self.set_main_property(GOLD_DANGO_INDEX)

        def become_cat(self, cat_type, flag):
            assert len(self.instances) == 1
            self.data = b'\x00' * len(self.data)
            self.set_main_property(cat_type)
            self.set_property('flag', flag)

        def become_gold_cat(self, flag):
            GOLD_CAT_INDEX = 0x89
            self.become_cat(GOLD_CAT_INDEX, flag)

        def become_silver_cat(self, flag):
            SILVER_CAT_INDEX = 0x88
            self.become_cat(SILVER_CAT_INDEX, flag)

        def become_surprise_pack(self, flag):
            SURPRISE_PACK_INDEX = 0x91
            self.data = b'\x00' * len(self.data)
            self.set_main_property(SURPRISE_PACK_INDEX)
            self.set_property('flag', flag)

        def become_pot(self):
            POT_INDEX = 0x192
            RYO_INDEX = 0x81
            self.data = b'\x00' * len(self.data)
            self.set_main_property(POT_INDEX)
            self.set_property('num_spawn', 4)
            self.set_property('spawn_id', RYO_INDEX)
            self.randomize_pot()

        def become_random_pickup(self):
            selector = random.randint(1, 3)
            if selector == 1:
                try:
                    flag = MapMetaObject.acquire_memory_flag()
                    self.become_surprise_pack(flag)
                except ValueError:
                    selector = random.randint(2, 3)
            if selector == 2:
                self.become_gold_dango()
            if selector == 3:
                self.become_pot()

        def randomize_pot(self):
            POT_INDEX = 0x192
            assert self.actor_id == POT_INDEX
            if not hasattr(MapMetaObject, '_pots'):
                pots = [e for mmo in MapMetaObject.sorted_rooms
                        for e in mmo.definitions
                        if e.old_actor_id == POT_INDEX]
                MapMetaObject._pots = pots
            chosen = random.choice(MapMetaObject._pots)
            self.set_property('spawn_id',
                              chosen.get_property_value('spawn_id'))
            old_num_spawn = chosen.get_property_value('num_spawn')
            spawn_range = old_num_spawn-1
            num_spawn = random.randint(1, old_num_spawn)
            while True:
                value = random.randint(0, spawn_range)
                num_spawn += value
                if spawn_range == 0 or value != spawn_range:
                    break
            self.set_property('num_spawn', num_spawn)

    class EntityInstance(EntityMixin):
        DATA_LENGTH = 0x14
        MAIN_PROPERTY_NAME = 'definition_index'
        DETAIL_PROPERTIES = ['x', 'y', 'z', 'rotx', 'roty', 'rotz']

        structure = {'definition_index':    {'index': (0xe, 0xf)},
                     'x':                   {'index': (0x0, 0x1)},
                     'z':                   {'index': (0x2, 0x3)},
                     'y':                   {'index': (0x4, 0x5)},
                     'rotx':                {'index': (0x6, 0x7)},
                     'rotz':                {'index': (0x8, 0x9)},
                     'roty':                {'index': (0xa, 0xb)},
                     }
        old_structure = structure

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
                if not hasattr(self, '_old_definition'):
                    self._old_definition = definition
                return definition
            return None

        @property
        def old_definition(self):
            return self._old_definition

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
        def is_pickup(self):
            return self.definition.is_pickup

        @property
        def is_enemy(self):
            return self.definition.is_enemy

        @property
        def is_unique(self):
            return len([i for i in self.parent.instances
                        if i.definition is self.definition]) == 1

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
            if (hasattr(self, '_property_cache') and
                    'definition' in self._property_cache):
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

        def spawn_door_blocker(self):
            BLOCKER_INDEX = 0x328
            if not hasattr(self, '_blocker_messages'):
                messages = set()
                for mmo in MapMetaObject.sorted_rooms:
                    for e in mmo.definitions:
                        if 'message' in e.structure:
                            messages.add(e.get_property_value('message'))
                self._blocker_messages = sorted(messages)
            candidates = [b for b in self.parent.definitions
                          if b.actor_id == BLOCKER_INDEX]
            if candidates:
                blocker = random.choice(candidates)
            else:
                data = b'\x00' * len(self.definition.data)
                blocker = self.parent.add_new_definition(data)
                blocker.set_main_property(BLOCKER_INDEX)
                blocker.set_property('message',
                                     random.choice(self._blocker_messages))
            data = b'\x00' * len(self.data)
            blocker_instance = self.parent.EntityInstance(data, self.parent)
            for attr in self.DETAIL_PROPERTIES:
                blocker_instance.set_property(attr,
                                              self.get_property_value(attr))
            blocker_instance.set_main_property(blocker.index)
            self.parent.spawn_groups[(-1,-1,-1)].append(blocker_instance)
            blocker_instance.clean()
            assert blocker_instance in self.parent.instances

        def yeet(self):
            self.data = self.parent.instances[0].data
            assert self.definition.actor_id == 0x8e

        def clean(self):
            if self.is_null:
                return
            self.data = self.data[:12] + b'\x08\x00' + self.data[14:]

        def validate_data(self):
            if self.is_null:
                return
            if self.definition is None:
                raise Exception(f'Instance {self.parent.warp_index:0>3x}-'
                                f'{self.definition_index:0>3x} is undefined.')
            assert self.data[12:14] == b'\x08\x00'
            assert self.definition.index == self.definition_index

    @classproperty
    def after_order(self):
        return [MessagePointerObject]

    @classproperty
    def VIRTUAL_RAM_OFFSET(self):
        return addresses.file00b_ram_offset

    @classproperty
    def POINTER_TABLE_OFFSET(self):
        return addresses.file00b_pointer_offset

    @classproperty
    def sorted_rooms(self):
        return sorted(
            (mmo for mmo in self.every if mmo.is_room),
            key=lambda x: x.warp_index)

    @classmethod
    def read_loading_files(self):
        main_code = self.get(self.MAIN_CODE_INDEX)
        main_code._data = main_code.get_decompressed()
        data_start = 0xffffffff
        data_end = 0
        routine_start = 0xffffffff
        routine_end = 0
        with BytesIO(main_code._data) as f:
            f.seek(self.convert_pointer(addresses.file00b_efile_offset))
            for entity_index in range(0x402):
                value = int.from_bytes(f.read(2), byteorder='big')
                self.ENTITY_FILES[entity_index] = value
            for warp_index in range(self.MAX_WARP_INDEX + 1):
                base_pointer = self.convert_pointer(
                        self.POINTER_TABLE_OFFSET+(warp_index*4))
                f.seek(base_pointer)
                pointer = int.from_bytes(f.read(4), byteorder='big')
                if pointer == 0:
                    continue
                f.seek(self.convert_pointer(pointer))
                metadata = f.read(self.METADATA_LENGTH)
                mmo_index = int.from_bytes(metadata[0x14:0x16],
                                           byteorder='big') - 1
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

                f.seek(self.convert_pointer(mmo.loading_pointer))
                routine_start = min(routine_start, f.tell())
                routine = f.read(0x24)
                routine_end = max(routine_end, f.tell())
                assert routine.startswith(self.LOADING_CODE_HEADER)
                self.LOADING_CODE_HEADER = routine[:0x12]
                assert routine.endswith(self.LOADING_CODE_FOOTER)
                assert len(routine) == len(
                    self.LOADING_CODE_HEADER + self.LOADING_CODE_FOOTER) + 2
                offset = int.from_bytes(routine[0x12:0x14], byteorder='big')
                f.seek(self.convert_pointer(
                    addresses.file00b_loading_bank | offset))
                data_start = min(data_start, f.tell())
                warp_loads = []
                while True:
                    value = int.from_bytes(f.read(2), byteorder='big')
                    if value == 0:
                        break
                    warp_loads.append(value)
                mmo.loading_files = warp_loads
                mmo.old_loading_files = list(mmo.loading_files)
                mmo.total_budget = max(mmo.total_size, mmo.MINIMUM_SAFE_BUDGET)
                mmo.enemy_budget = mmo.enemy_size
                mmo.pickup_budget = mmo.pickup_size
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

            if mmo.data_has_changed:
                mmo.validate_budget()
                mmo.validate_entity_files()
            values = []
            for l in mmo.loading_files:
                if l in mmo.misc_data.loading_files:
                    raise Exception(f'File {l:0>3x} specified in both meta '
                                    f'and misc loading data for room '
                                    f'{warp_index:0>3x}.')
                if l in values and (VERBOSE or DEBUG_MODE):
                    print(f'Warning: Removing duplicate file {l:0>3x} from '
                          f'room {warp_index:0>3x}')
                    continue
                values.append(l)
            mmo.loading_files = values
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
            list_pointer = self.convert_pointer(data_start+index)
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
            loading_pointer = self.convert_pointer(routine_start +
                                                   routine_offset)
            mmo.loading_pointer = loading_pointer | 0x80000000

            mmo.instance_offset = (
                len(mmo.definitions) * mmo.EntityDefinition.DATA_LENGTH)
            instance_data, _ = mmo.get_instance_data()
            mmo.footer_offset = mmo.instance_offset + len(instance_data)
            mmo.ending_offset = mmo.footer_offset + self.ENTITY_FOOTER_LENGTH

            metadata_length = max(max(self.METADATA_STRUCTURE.values()))
            assert metadata_length == self.METADATA_LENGTH
            metadata = b'\x00' * metadata_length
            for (attribute, (a, b)) in self.METADATA_STRUCTURE.items():
                length = b-a
                value = getattr(mmo, attribute)
                value = value.to_bytes(length=length, byteorder='big')
                metadata = metadata[:a] + value + metadata[b:]

            base_pointer = self.convert_pointer(
                    self.POINTER_TABLE_OFFSET+(warp_index*4))
            f.seek(base_pointer)
            pointer = int.from_bytes(f.read(4), byteorder='big')
            assert pointer > 0
            f.seek(self.convert_pointer(pointer))
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
    @lru_cache(maxsize=None)
    def get_by_warp_index(self, index):
        assert self is MapMetaObject
        choices = [mmo for mmo in MapMetaObject.every
                   if hasattr(mmo, 'warp_index')
                   and mmo.warp_index == index]
        if not choices:
            return None
        assert len(choices) == 1
        return choices[0]

    @classmethod
    def get_entity_by_signature(self, signature, convert=True):
        assert self is MapMetaObject
        if convert and get_global_label() == 'MN64_EN' and \
                signature in self.JP_EN_NODE_MAPPING:
            signature = self.JP_EN_NODE_MAPPING[signature]
        if signature in MapMetaObject.entity_signatures:
            return MapMetaObject.entity_signatures[signature]
        warp_index = signature.split('-')[0]
        mmo = MapMetaObject.get_by_warp_index(int(warp_index, 0x10))
        for e in mmo.entities:
            if e.signature == signature:
                return e
        raise Exception(f'No entity: {signature}')

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
                    mmo.definitions = []
                    mmo.spawn_groups = {}
                    previous_entity = None
                    mmo.footer = b''
                    spawn_group = (-1, -1, -1)
                elif line.startswith('!load '):
                    line = line[6:]
                    values = [int(v, 0x10) for v in line.split()]
                    mmo.loading_files = values
                elif line.startswith('!meta '):
                    _, attribute, value = line.split()
                    value = int(value, 0x10)
                    assert attribute in self.METADATA_STRUCTURE
                    assert hasattr(mmo, attribute)
                    if attribute == 'file_index' and mmo.file_index != value:
                        raise Exception(f'Cannot change file index '
                                        f'{mmo.file_index:0>3x}.')
                    setattr(mmo, attribute, value)
                elif line.startswith('!misc '):
                    _, attribute, value = line.split(' ', 2)
                    assert attribute in mmo.misc_data.STRUCTURE
                    if ',' in value:
                        value = [int(v, 0x10) for v in value.split(',')]
                    elif ' ' in value:
                        value = bytes(int(v, 0x10) for v in value.split())
                    else:
                        assert len(value) <= 8
                        value = int(value, 0x10)
                    setattr(mmo.misc_data, attribute, value)
                elif line.upper().startswith('+GROUP'):
                    coords = line.split()[-1]
                    x, z, y = coords.split(',')
                    spawn_group = (int(x, 0x10), int(z, 0x10), int(y, 0x10))
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
                elif ':' in line:
                    previous_entity = mmo.import_line(line, spawn_group)
                    assert not mmo.footer
                else:
                    line = [int(v, 0x10).to_bytes(length=2, byteorder='big')
                            for v in line.split()]
                    line = b''.join(line)
                    if mmo.footer:
                        raise Exception(
                            f'Extraneous data: ROOM {mmo.warp_index:0>3X}')
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

    @classmethod
    def set_pemopemo_destination(self, room, x, z, y, direction):
        PEMOPEMO_ENTITY = 0x335
        PEMOPEMO_FILE_INDEX = self.ENTITY_FILES[PEMOPEMO_ENTITY]-1
        assert PEMOPEMO_FILE_INDEX == 0x42

        mmo = MapMetaObject.get(PEMOPEMO_FILE_INDEX)
        if hasattr(mmo, '_data'):
            data = mmo._data
        else:
            data = mmo.get_decompressed()
        f = BytesIO(data)

        def format_two_bytes(value):
            return f'{value>>8:0>2x} {value&0xff:0>2x}'

        parameters = {
            'direction': direction, 'room': room,
            'x': x, 'z': z, 'y': y,
            }
        parameters = {k: format_two_bytes(v) for (k, v) in parameters.items()}

        if get_global_label() == 'MN64_JP':
            write_patch(f, 'patch_pemopemo_destination_042.txt',
                        parameters=parameters, noverify=True)
        elif get_global_label() == 'MN64_EN':
            write_patch(f, 'patch_pemopemo_destination_042_en.txt',
                        parameters=parameters, noverify=True)

        f.seek(0)
        mmo._data = f.read()
        f.close()

    @classmethod
    def free_memory_flag(self, flag):
        self.available_memory_flags.add(flag)

    @classmethod
    def acquire_memory_flag(self):
        chosen = min(self.available_memory_flags)
        self.available_memory_flags.remove(chosen)
        return chosen

    def __repr__(self):
        if self.warp_index is not None:
            header = f'ROOM {self.warp_index:0>3X}: '
        else:
            header = f'ROOM: '
        header += (f'{self.index:0>3x},{self.pointer:0>5x}->'
                   f'{self.reference_pointer:0>8x}')
        if self.room_name:
            header += f'  # {self.debug_index} - {self.room_name}'
        else:
            header += f'  # {self.debug_index}'
        header += '\n# {0:25} {1}'.format('Total Memory Used', self.total_size)
        if self.warp_index in MapCategoryData.special_idle_animations:
            value = MapCategoryData.special_idle_animations[self.warp_index]
            header += '\n# {0:25} {1:0>4x}'.format('Idle Animation', value)
        for attr in ('instance_offset', 'footer_offset',
                     'ending_offset', 'loading_pointer'):
            if not hasattr(self, attr):
                continue
            a, b = self.METADATA_STRUCTURE[attr]
            length = (b-a)*2
            value = ('{0:0>%sx}' % length).format(getattr(self, attr))
            header += f'\n# {attr:25} {value}'

        for attr in ('file_index', 'persist_actor_ptr', 'event_source_ptr'):
            if not hasattr(self, attr):
                continue
            a, b = self.METADATA_STRUCTURE[attr]
            length = (b-a)*2
            value = ('{0:0>%sx}' % length).format(getattr(self, attr))
            header += f'\n# !meta {attr:19} {value}'

        for attr in sorted(MapCategoryData.STRUCTURE):
            if self.warp_index is None:
                break
            value = self.misc_data.get_pretty_attribute(attr)
            header += f'\n# !misc {attr:19} {value}'

        if hasattr(self, 'loading_files') and self.loading_files:
            loading_files = ' '.join([f'{v:0>3x}' for v in self.loading_files])
            header += f'\n!load {loading_files}'

        s = header + '\n\n'
        if hasattr(self, 'definitions'):
            definitions = self.definitions
            h = '# DEFINITIONS\n'
            h += '\n'.join(map(str, definitions))
            h += '\n\n# INSTANCES\n'
            for group, instances in sorted(self.spawn_groups.items()):
                s2 = '\n'.join(map(str, instances))
                if instances and group != (-1, -1, -1):
                    label = ','.join([f'{g:0>2x}' for g in group])
                    s2 = f'+GROUP {label}\n{s2}'
                    s2 = s2.replace('\n', '\n  ')
                h += s2 + '\n'
            h += '\n\n# FOOTER\n'
            h += f'# Spawn group dimensions: ' \
                f'{self.groups_x:0>2x},{self.groups_z:0>2x},{self.groups_y:0>2x}\n'
            h += pretty_hexify(self.footer).replace('\n', ' ') + '\n'
            while '\n\n\n' in h:
                h = h.replace('\n\n\n', '\n\n')
            s += h

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
    def misc_data(self):
        return MapCategoryData.get_by_warp_index(self.warp_index)

    @property
    def metasize(self):
        return MetaSizeObject.get(self.index)

    @property
    def total_size(self):
        if not hasattr(self, 'loading_files'):
            return None
        loading_files = list(self.loading_files)
        loading_files += [l for l in self.misc_data.loading_files if l > 0]
        assert 0 not in loading_files
        return sum([MetaSizeObject.get(index-1).effective_metasize
                    for index in loading_files])

    @property
    def enemy_size(self):
        assert self.total_size
        enemy_files = set(self.loading_files) & self.ENEMY_FILES
        return sum([MetaSizeObject.get(index-1).effective_metasize
                    for index in enemy_files])

    @property
    def pickup_size(self):
        assert self.total_size
        pickup_files = set(self.loading_files) & self.PICKUP_FILES
        return sum([MetaSizeObject.get(index-1).effective_metasize
                    for index in pickup_files])

    @property
    def other_size(self):
        return self.total_size - (self.enemy_size + self.pickup_size)

    @property
    def data(self):
        if hasattr(self, '_data'):
            return self._data
        if self.is_room:
            data = b''
            for e in self.definitions:
                data += e.data

            definitions_length = len(data)
            instance_data, group_offsets = self.get_instance_data()
            data += instance_data

            data += self.footer
            for x in range(self.groups_x):
                for z in range(self.groups_z):
                    for y in range(self.groups_y):
                        if (x, z, y) not in group_offsets:
                            data += b'\x00\x00\x00\x00'
                            continue
                        data += b'\x08\x00'
                        value = group_offsets[x,z,y] + definitions_length
                        data += value.to_bytes(length=2, byteorder='big')

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
    def debug_index(self):
        if self.warp_index is not None:
            category_index = max(i for i in self.DEBUG_WARP_CATEGORIES
                                 if i <= self.warp_index)
            category_name = self.DEBUG_WARP_CATEGORIES[category_index]
            return f'{category_name} {self.warp_index-category_index}'
        else:
            return f'STAGE.NO {self.index}'

    @cached_property
    def exits(self):
        return [e for e in self.instances if e.is_exit]

    @property
    def instances(self):
        entities = []
        for key in sorted(self.spawn_groups):
            entities += self.spawn_groups[key]
        return entities

    @property
    def entities(self):
        return self.definitions + self.instances

    @property
    def enemies(self):
        return [i for i in self.instances if i.is_enemy]

    @property
    def groups_x(self):
        return int.from_bytes(self.footer[0x14:0x16], byteorder='big')

    @property
    def groups_z(self):
        return int.from_bytes(self.footer[0x16:0x18], byteorder='big')

    @property
    def groups_y(self):
        return int.from_bytes(self.footer[0x18:0x1a], byteorder='big')

    @property
    def group_data(self):
        return b''

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
        if hasattr(self, 'footer'):
            return self.entities

        self.footer = None
        data = self.get_decompressed()
        if data is None:
            return None

        definition_segment = data[:self.instance_offset]
        instance_segment = data[self.instance_offset:self.footer_offset]
        self.footer = data[self.footer_offset:self.ending_offset]
        group_data = data[self.ending_offset:]
        assert len(data) >= self.ending_offset

        self.spawn_groups = {}
        self.definitions = []
        while definition_segment:
            entity = self.EntityDefinition(
                definition_segment[:self.EntityDefinition.DATA_LENGTH], self)
            definition_segment = \
                definition_segment[self.EntityDefinition.DATA_LENGTH:]
            self.definitions.append(entity)

        group_offsets = {(-1, -1, -1): 0}
        for x in range(self.groups_x):
            for z in range(self.groups_z):
                for y in range(self.groups_y):
                    group, group_data = group_data[:4], group_data[4:]
                    if group == b'\x00\x00\x00\x00':
                        continue
                    assert group[:2] == b'\x08\x00'
                    offset = int.from_bytes(group[2:], byteorder='big')
                    group_offsets[(x, z, y)] = offset - self.instance_offset

        for key in group_offsets:
            offset = group_offsets[key]
            data = instance_segment[offset:]
            spawn_group = []
            while True:
                edata, data = (data[:self.EntityInstance.DATA_LENGTH],
                               data[self.EntityInstance.DATA_LENGTH:])
                entity = self.EntityInstance(edata, self)
                if entity.is_null:
                    break
                spawn_group.append(entity)
                self.spawn_groups[key] = spawn_group
        return self.entities

    def get_instance_data(self):
        group_offsets = {}
        data = b''
        for key in sorted(self.spawn_groups):
            if not self.spawn_groups[key]:
                continue
            group_offsets[key] = len(data)
            for e in self.spawn_groups[key]:
                data += e.data
            data += b'\x00' * self.EntityInstance.DATA_LENGTH
        if not data:
            data = b'\x00' * self.EntityInstance.DATA_LENGTH
        return data, group_offsets

    def add_new_definition(self, data):
        definition_indexes = {d.index for d in self.definitions}
        instance_indexes = {d.index for d in self.instances}
        new_index = max(definition_indexes) + 1
        if new_index in instance_indexes:
            for i in self.instances:
                i.index += 1
            instance_indexes = {d.index for d in self.instances}
        assert new_index not in instance_indexes
        definition = self.EntityDefinition(data, self, index=new_index)
        self.definitions.append(definition)
        assert self.entities.index(definition) == definition.index
        return definition

    def import_line(self, line, spawn_group):
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

        new_entity = entity_type(new_data, self, index, validate=False)
        if isinstance(new_entity, MapMetaObject.EntityDefinition):
            self.definitions.append(new_entity)
            self.definitions = sorted(self.definitions, key=lambda e: e.index)
        else:
            if spawn_group not in self.spawn_groups:
                self.spawn_groups[spawn_group] = []
            self.spawn_groups[spawn_group].append(new_entity)
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
            raise Exception(f'No free space: {self.index:x}')
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

    def force_allocate(self, start, length):
        if length == 0:
            return
        free_space = [(a, b) for (a, b) in sorted(MapMetaObject.free_space)
                      if a <= start <= b]
        assert len(free_space) == 1
        a, b = free_space[0]
        assert b - start >= length
        MapMetaObject.free_space.remove((a, b))
        if start > a:
            MapMetaObject.free_space.append((a, start))
        if start + length < b:
            MapMetaObject.free_space.append((start+length, b))
        return start

    def force_write(self):
        assert self.is_compressed
        compressed = recompress(self.data)
        assert len(compressed) <= len(self._cached_compressed)
        while len(compressed) < len(self._cached_compressed):
            compressed += b'\xff'
        address = self.reference_pointer & 0x7fffffff
        self.force_allocate(address, len(compressed))
        f = get_open_file(get_outfile())
        f.seek(address)
        f.write(compressed)
        self.relocated = True

    def compress_and_write(self):
        if self.index in self.FORCE_OLD_POINTER:
            if not self.data_has_changed:
                assert self.get_compressed() == self._cached_compressed
                self.force_allocate(self.reference_pointer & 0x7fffffff,
                                    len(self._cached_compressed))
                self.relocated = True
                return
            else:
                #if not self.is_room:
                #    print(f'NOTICE: Force writing new data to '
                #          f'file {self.index+1:0>3x}.')
                return self.force_write()

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

        if self.index == MapCategoryData.ROOM_DATA_INDEX:
            old_length = len(self.get_compressed())
            assert len(data) <= old_length
            data += b'\x00' * (old_length-len(data))
        else:
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

    def validate_budget(self):
        # Some actors depend on files of other actors (i.e. pink robot spawner)
        # So you can't just remove files blindly
        # We add these files back in EXTRA_DEPENDENCIES
        if 'enemizer' not in get_activated_codes():
            return
        used_files = {self.ENTITY_FILES[i.definition.actor_id]
                      for i in self.instances}
        maybe_cut = set(self.loading_files) & \
                (self.ENEMY_FILES | self.PICKUP_FILES)
        for index in sorted(maybe_cut - used_files):
            if VERBOSE or DEBUG_MODE:
                print(f'REMOVING {index:0>3x} from {self.warp_index:0>3x}.')
            for d in self.definitions:
                if self.ENTITY_FILES[d.actor_id] == index:
                    if VERBOSE or DEBUG_MODE:
                        print(f'REMOVING {d.signature} from '
                              f'{self.warp_index:0>3x}.')
                    d.remove()
            if index in self.old_loading_files and \
                    index not in self.old_instance_loading_files:
                continue
            self.loading_files.remove(index)

    def validate_entity_files(self):
        for e in self.instances:
            if e.is_null:
                continue
            actor_id = e.definition.actor_id
            if actor_id not in self.ENTITY_FILES:
                continue
            file_index = self.ENTITY_FILES[actor_id]
            if file_index == 0:
                continue
            if file_index not in self.loading_files:
                if VERBOSE or DEBUG_MODE:
                    print(f'Warning: Entity {e.definition.signature} requires '
                          f'file {file_index:0>3x}; adding automatically.')
                self.loading_files.append(file_index)
            if actor_id in self.EXTRA_DEPENDENCIES:
                for file_index in self.EXTRA_DEPENDENCIES[actor_id]:
                    if file_index not in self.loading_files:
                        if VERBOSE or DEBUG_MODE:
                            print(f'Warning: Entity {e.definition.signature} '
                                  f'requires extra file {file_index:0>3x}; '
                                  f'adding automatically.')
                        self.loading_files.append(file_index)
        if self.warp_index == self.MUSASHI_IGA_TUNNEL \
                and get_global_label() == 'MN64_EN':
            assert 0x20 in self.loading_files

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

    def matches_bgm(self, other):
        assert self.is_room
        assert other.is_room
        if self.misc_data.bgm == other.misc_data.bgm:
            return True
        for group in self.BGM_GROUPS:
            if self.misc_data.bgm in group and other.misc_data.bgm in group:
                return True
        return False

    def get_nearest_exit(self, x, y, z):
        def distance(a, b):
            x1, y1, z1 = a
            x2, y2, z2 = b
            return (((x1-x2)**2) + ((y1-y2)**2) + ((z1-z2)**2)) ** 0.5

        x1 = x if x < 0x8000 else x - 0x10000
        y1 = y if y < 0x8000 else y - 0x10000
        z1 = z if z < 0x8000 else z - 0x10000
        coords = {}
        for door in self.exits:
            x2 = door.get_property_value('x')
            y2 = door.get_property_value('y')
            z2 = door.get_property_value('z')
            x2 = x2 if x2 < 0x8000 else x2 - 0x10000
            y2 = y2 if y2 < 0x8000 else y2 - 0x10000
            z2 = z2 if z2 < 0x8000 else z2 - 0x10000
            coords[x2, y2, z2] = door

        sorted_coords = sorted(
                coords, key=lambda c: (distance((x1, y1, z1), c), c))
        return coords[sorted_coords[0]]

    def preprocess(self):
        self.get_compressed()
        if self.index > 0 and not self.get(self.index-1).is_rom_split:
            assert self.data_pointer >= self.get(self.index-1).data_pointer

        if self.is_room:
            self.get_entities()
            self.old_instance_loading_files = set()
            for i in self.instances:
                loading_file = self.ENTITY_FILES[i.definition.actor_id]
                if loading_file != 0:
                    self.old_instance_loading_files.add(loading_file)
            assert not self.data_has_changed

    def preclean(self):
        if self.index >= MapCategoryData.ROOM_DATA_INDEX:
            self.deallocate()

    def cleanup(self):
        if self.is_room and self.data_has_changed:
            self.validate_entities()
        if (self.index == MapCategoryData.ROOM_DATA_INDEX
                and self.data_has_changed):
            if any(mmo.misc_data.has_changed
                   for mmo in MapMetaObject.every if mmo.is_room):
                print(f'WARNING: Modifying miscellaneous data in file '
                      f'{self.index:0>3x} may result in instability.')
        if self.index >= MapCategoryData.ROOM_DATA_INDEX:
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
        if (self.index <= self.MAIN_CODE_INDEX and self.reference_pointer_be
                != self.old_data['reference_pointer_be']):
            old_reference = self.old_data['reference_pointer']
            print(f'WARNING: File {self.index:0>3x} has moved from '
                  f'{old_reference:x} to {self.reference_pointer:x}. '
                  f'This may result in instability.')

    @classmethod
    def preprocess_all(cls):
        MapMetaObject.free_space = [(addresses.free_space_start,
                                     addresses.free_space_end)]
        for mmo in MapMetaObject.every:
            mmo.warp_index = None
        cls.read_loading_files()
        super().preprocess_all()

    @classmethod
    def full_preclean(cls):
        MapCategoryData.full_preclean()
        super().full_preclean()

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

        if get_global_label() == 'MN64_EN':
            mmo = MapMetaObject.get_by_warp_index(cls.MUSASHI_IGA_TUNNEL)
            if 0x20 not in mmo.loading_files:
                print(f'WARNING: DOUCHU 5 requires loading file 020 on the '
                      f'English version of Mystical Ninja Starring Goemon.')

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


class MapCategoryData(ConvertPointerMixin):
    ROOM_DATA_INDEX = 0xa

    CATEGORY_RANGES = [
        (0x000, 0x05a),
        (0x12c, 0x15e),
        (0x15e, 0x190),
        (0x190, 0x1e4),
        (0x05a, 0x080),
        (0x080, 0x12c),
        ]
    DATA_LENGTHS = [
        20, 8, 8, 4, 4, 2, 2,
        ]

    STRUCTURE = {
        'graphics1':        (0, (0, 8)),
        'loading_unknown':  [(0, ( 8, 12)),
                             (0, (12, 16)),
                             (0, (16, 20))],
        'graphics2':        (1, (0, 8)),
        'loading_files':    [(2, (0, 2)),
                             (2, (2, 4)),
                             (2, (4, 6)),
                             (2, (6, 8))],
        'bsp_plane_data':   (3, (0, 4)),
        'bsp_tree':         (4, (0, 4)),
        'bgm':              (5, (0, 2)),
        'skybox_index':     (6, (0, 2)),
        }

    datas_by_warp_index = {}

    def __init__(self, warp_index):
        self.warp_index = warp_index
        self.read_attributes()
        assert self.special_idle_animations

    @classproperty
    def VIRTUAL_RAM_OFFSET(self):
        # Location in RAM where file 00a is
        return addresses.file00a_ram_offset

    @clached_property
    def POINTER_POINTERS(self):
        return [addresses.file00a_pointer_offset + (i*4*6) for i in range(7)]

    @classproperty
    def every(self):
        return [self.get_by_warp_index(mmo.warp_index)
                for mmo in MapMetaObject.sorted_rooms]

    @classmethod
    def get_by_warp_index(self, warp_index):
        if warp_index in self.datas_by_warp_index:
            mcd = self.datas_by_warp_index[warp_index]
            assert mcd.warp_index == warp_index
            return mcd
        mcd = MapCategoryData(warp_index)
        self.datas_by_warp_index[warp_index] = mcd
        return self.get_by_warp_index(warp_index)

    @property
    def has_changed(self):
        for attribute in self.old_data:
            if self.old_data[attribute] != getattr(self, attribute):
                return True
        return False

    def read_attribute(self, section, indexes):
        a, b = indexes
        data = MapCategoryData.get_data(self.warp_index, section)[a:b]
        if len(data) > 4:
            return data
        return int.from_bytes(data, byteorder='big')

    def read_attributes(self):
        if not hasattr(self, 'old_data'):
            self.old_data = {}
        for attribute, directions in self.STRUCTURE.items():
            if isinstance(directions, list):
                setattr(self, attribute,
                        [self.read_attribute(section, indexes)
                         for (section, indexes) in directions])
            else:
                section, indexes = directions
                setattr(self, attribute,
                        self.read_attribute(section, indexes))
            if attribute not in self.old_data:
                value = getattr(self, attribute)
                if isinstance(value, list):
                    value = list(value)
                self.old_data[attribute] = value

    def get_pretty_attribute(self, attribute):
        directions = self.STRUCTURE[attribute]
        value = getattr(self, attribute)
        if not isinstance(directions, list):
            directions = [directions]
            value = [value]
        assert len(directions) == len(value)
        result = []
        for d, v in zip(directions, value):
            if isinstance(v, int):
                section, (a, b) = d
                length = (b-a) * 2
                result.append(('{0:0>%sx}' % length).format(v))
            else:
                result.append(hexify(v))
        return ','.join(result)

    def save_attribute(self, section, indexes, value):
        a, b = indexes
        if isinstance(value, int):
            value = value.to_bytes(length=(b-a), byteorder='big')
        data = MapCategoryData.get_data(self.warp_index, section)
        newdata = data[:a] + value + data[b:]
        room_category, _ = self.convert_warp_to_category(self.warp_index)
        if data != newdata and section == 6 and room_category in [0, 3]:
            assert not 0x5a <= self.warp_index < 0x190
            raise Exception(f'Room {self.warp_index:0>3x} cannot change '
                            f'misc data in section {section}.')

        MapCategoryData.save_data(self.warp_index, section, newdata)

    def save_attributes(self):
        assert not hasattr(self, '_saved')
        self._saved = True
        for attribute, directions in self.STRUCTURE.items():
            value = getattr(self, attribute)
            if value == self.old_data[attribute]:
                continue
            if isinstance(directions, list):
                assert len(directions) == len(value)
                for (d, v) in zip(directions, value):
                    section, indexes = d
                    self.save_attribute(section, indexes, v)
            else:
                section, indexes = directions
                self.save_attribute(section, indexes, value)

    def verify_attributes(self):
        assert hasattr(self, '_saved')
        verify = {attribute: getattr(self, attribute)
                  for attribute in self.STRUCTURE}
        self.read_attributes()
        for attribute in self.STRUCTURE:
            if verify[attribute] != getattr(self, attribute):
                raise Exception(error)

    def randomize(self):
        room_category, _ = self.convert_warp_to_category(self.warp_index)
        for attribute in self.STRUCTURE:
            if attribute == 'unknown6' and room_category in {0, 3}:
                continue
            value = getattr(self, attribute)
            if isinstance(value, int):
                oldvalue = value
                while value == oldvalue:
                    value += random.randint(-value, 0x10)
            elif isinstance(value, list):
                random.shuffle(value)
            else:
                value = list(value)
                random.shuffle(value)
                value = bytes(value)
            setattr(self, attribute, value)

    @classproperty
    def data(self):
        if hasattr(MapCategoryData, '_data'):
            return MapCategoryData._data

        mmo = MapMetaObject.get(MapCategoryData.ROOM_DATA_INDEX)
        MapCategoryData._data = BytesIO(mmo.get_decompressed())
        return MapCategoryData.data

    @clached_property
    def special_idle_animations(self):
        self.data.seek(self.convert_pointer(addresses.file00a_idle_offset))
        result = {}
        while True:
            room_index = self.data.read(2)
            if room_index == b'\xff\xff':
                break
            room_index = int.from_bytes(room_index, byteorder='big')
            result[room_index] = int.from_bytes(self.data.read(2),
                                                byteorder='big')
        return result

    @classmethod
    def convert_warp_to_category(self, warp_index):
        for n, (a, b) in enumerate(self.CATEGORY_RANGES):
            if a <= warp_index < b:
                room_category = n
                category_index = warp_index - a
                break
        else:
            raise Exception(f'Warp index {warp_index:0>3x} has no category.')
        return room_category, category_index

    @classmethod
    def get_data_address(self, warp_index, section):
        room_category, category_index = \
                self.convert_warp_to_category(warp_index)

        mmo = MapMetaObject.get(self.ROOM_DATA_INDEX)
        pointer_pointer = self.POINTER_POINTERS[section]
        pointer = self.convert_pointer(pointer_pointer) + (room_category*4)
        self.data.seek(pointer)
        pointer = self.convert_pointer(self.data.read(4))
        data_length = self.DATA_LENGTHS[section]
        pointer += category_index * data_length
        return pointer

    @classmethod
    def get_data(self, warp_index, section):
        pointer = self.get_data_address(warp_index, section)
        self.data.seek(pointer)
        data_length = self.DATA_LENGTHS[section]
        data = self.data.read(data_length)
        return data

    @classmethod
    def save_data(self, warp_index, section, data):
        assert len(data) == self.DATA_LENGTHS[section]
        pointer = self.get_data_address(warp_index, section)
        self.data.seek(pointer)
        self.data.write(data)

    @classmethod
    def full_preclean(self):
        assert not hasattr(MapMetaObject, 'cleaned')
        assert not hasattr(MapMetaObject, 'precleaned')

        for mcd in self.every:
            mcd.save_attributes()
        for mcd in self.every:
            mcd.verify_attributes()

        mmo = MapMetaObject.get(self.ROOM_DATA_INDEX)
        self.data.seek(0)
        mmo._data = self.data.read()
        self.data.close()


class WarpObjectMixin:
    def __repr__(self):
        if not hasattr(self, 'dest_room'):
            self.__class__.create_properties()
        s = f'{self.description}\n'
        for attr in ['dest_room', 'dest_x', 'dest_z', 'dest_y', 'direction']:
            value = getattr(self, attr)
            if attr == 'dest_room':
                room = MapMetaObject.get_by_warp_index(value)
                if room:
                    room_name = room.room_name
                else:
                    room_name = 'None'
                s += f'  {attr}: {value:0>4x} {room_name}\n'
            else:
                s += f'  {attr}: {value:0>4x}\n'
        for attr in ['misc_exit_id', 'misc_unknown']:
            value = getattr(self, attr)
            s += f'  {attr}: {value:0>2x}\n'
        return s.strip()

    @classmethod
    def create_properties(self):
        attrs = ['dest_room', 'dest_x', 'dest_z', 'dest_y', 'direction']
        if hasattr(self, attrs[0]):
            return
        attr_strs = [f'{attr}_str' for attr in attrs]
        for attr, attr_str in zip(attrs, attr_strs):
            get_lambda = lambda o, a=attr_str: int.from_bytes(
                    getattr(o, a), byteorder='big')
            set_lambda = lambda o, v, a=attr_str: setattr(
                    o, a, v.to_bytes(length=2, byteorder='big'))
            setattr(self, attr, property(get_lambda, set_lambda))

    def infer_warp_point(self):
        if not hasattr(self, 'dest_room'):
            self.__class__.create_properties()
        mmo = MapMetaObject.get_by_warp_index(self.dest_room)
        door = mmo.get_nearest_exit(self.dest_x, self.dest_y, self.dest_z)
        pair = door.exit_pair
        assert len(pair.parent.exits) == 1
        attrs = ['dest_room', 'dest_x', 'dest_z', 'dest_y', 'direction']
        for attr in attrs:
            value = pair.definition.get_property_value(attr)
            setattr(self, attr, value)

    def preclean(self):
        if not (hasattr(self, 'needs_update') and self.needs_update):
            return
        self.infer_warp_point()


class SaveWarpObject(WarpObjectMixin, TableObject): pass
class DragonWarpObject(WarpObjectMixin, TableObject): pass


class MessageFileObject(TableObject):
    def get_file_index(self):
        return int.from_bytes(self.file_index_str, byteorder='big')

    def set_file_index(self, value):
        self.file_index_str = value.to_bytes(length=2, byteorder='big')

    def del_file_index(self):
        self.file_index_str = self.old_data['file_index_str']

    file_index = property(get_file_index, set_file_index, del_file_index)


class MessagePointerObject(TableObject):
    NUM_PARAMETERS = {
            0x08: 0,
            0x10: 1,
            0x11: 0,
            0x12: 0,
            0x22: 2,
        }
    MESSAGE_TERMINATE_OPCODE = 0x08
    MESSAGE_TEXT_OPCODE = 0x10
    COMMENTS = {
            0x04: 'At RAM address {0:0>8x}...',
            0x08: 'End Message',
            0x09: 'Store Value: {0:0>8x}',
            0x10: 'Print Text',
            0x22: 'If Flag {0:0>4x}, Jump To {1:0>8x}',
        }

    def __repr__(self):
        return self.get_pretty()

    @classmethod
    def decode(self, word):
        manual_map = {
            0x0000: ' ',
            0x0001: '!',
            0x0007: "'",
            0x000c: ',',
            0x000e: '.',
            0x000f: '/',
            }
        value = int.from_bytes(word, byteorder='big')
        if value in manual_map:
            return manual_map[value]
        if not value:
            return ' '
        if value & 0xFF00 == 0:
            if 65 <= value <= 90:
                return chr(value).lower()
            elif 65 <= value + 0x20 <= 90:
                return chr(value + 0x20)
            elif 0x11 <= value <= 0x19:
                return str(value - 0x10)
        s = '{%s}' % f'{value:0>4x}'
        if value == 0xffc4 and False:
            return '\n' + s
        if value == 0xffff:
            return s + '\n'
        return s

    @classmethod
    def get_text(self, f, pointer=None):
        old_pointer = f.tell()
        if pointer is not None:
            pointer &= 0xffffff
            f.seek(pointer)
        s = ''
        while True:
            word = f.read(2)
            if len(word) < 2:
                break
            if word == b'\xff\xff':
                break
            s += self.decode(word)
        f.seek(old_pointer)
        return s

    def get_message_pointer(self):
        return int.from_bytes(self.message_pointer_str, byteorder='big')

    def set_message_pointer(self, value):
        self.message_pointer_str = value.to_bytes(length=3, byteorder='big')

    def del_message_pointer(self):
        self.message_pointer_str = self.old_data['message_pointer_str']

    message_pointer = property(
            get_message_pointer, set_message_pointer, del_message_pointer)

    @property
    def file_index(self):
        return MessageFileObject.get(self.index).file_index

    @property
    def header(self):
        return (f'MESSAGE {self.index:0>3x}: '
                f'{self.file_index:0>3x}-{self.message_pointer:0>4x}')

    def get_message(self):
        self.message = []
        self.message_texts = {}
        if self.file_index == 0:
            return

        mmo = MapMetaObject.get(self.file_index-1)
        if hasattr(mmo, '_data'):
            data = mmo._data
        else:
            data = mmo.get_decompressed()
        f = BytesIO(data)
        f.seek(self.message_pointer)
        while True:
            opcode = f.read(4)
            if not opcode:
                break
            if opcode == b'\x00\x00\x00\x00':
                break
            assert opcode[:3] == b'\x00\x00\x80'
            opcode = opcode[-1]
            if opcode in self.NUM_PARAMETERS:
                num_parameters = self.NUM_PARAMETERS[opcode]
            else:
                num_parameters = 1
            arguments = tuple([int.from_bytes(f.read(4), byteorder='big')
                               for _ in range(num_parameters)])
            self.message.append((opcode, arguments))
            if opcode == self.MESSAGE_TERMINATE_OPCODE:
                break
            if opcode == self.MESSAGE_TEXT_OPCODE:
                assert len(arguments) == 1
                pointer = arguments[0]
                assert pointer >> 24 in (0, 8, 9)
                text = self.get_text(f, pointer)
                self.message_texts[pointer] = text
        f.close()

    def get_pretty(self):
        s = ''
        for opcode, arguments in self.message:
            argstr = ','.join([f'{a:0>8x}' for a in arguments])
            line = f'{opcode:0>2x}: {argstr}'
            if opcode in self.COMMENTS:
                comment = self.COMMENTS[opcode].format(*arguments)
                line = f'{line:23}# {comment}'
            s += line + '\n'
            if opcode == self.MESSAGE_TEXT_OPCODE:
                text = self.message_texts[arguments[0]]
                text = f'|{text}|'
                text = text.replace('\n', '\n      ')
                text = '      ' + text.strip()
                s += text + '\n'
        s = s.strip()
        s = '  ' + s.replace('\n', '\n  ')
        s = f'{self.header}\n{s}'
        return s.strip()

    def get_bytecode(self):
        s = b''
        for opcode, arguments in self.message:
            s += (opcode | 0x8000).to_bytes(length=4, byteorder='big')
            for a in arguments:
                s += a.to_bytes(length=4, byteorder='big')
        return s

    def preprocess(self):
        self.reallocate = False
        self.get_message()
        self.old_bytecode = self.get_bytecode()

    def cleanup(self):
        if not self.reallocate:
            assert self.message_pointer_str == \
                    self.old_data['message_pointer_str']
            assert self.get_bytecode() == self.old_bytecode

    @classmethod
    def full_cleanup(self):
        super().full_cleanup()

        file_indexes = {mpo.file_index for mpo in MessagePointerObject.every}
        file_indexes.discard(0)
        for file_index in sorted(file_indexes):
            mpos = [mpo for mpo in MessagePointerObject.every
                    if mpo.file_index == file_index
                    and mpo.reallocate is True]
            if not mpos:
                continue
            free_space = set()
            for mpo in mpos:
                free_space.add((mpo.message_pointer,
                                mpo.message_pointer + len(mpo.old_bytecode)))
            free_space = consolidate_free_space(free_space)
            mmo = MapMetaObject.get(file_index-1)
            if hasattr(mmo, '_data'):
                data = mmo._data
            else:
                data = mmo.get_decompressed()
            f = BytesIO(data)
            for mpo in mpos:
                bytecode = mpo.get_bytecode()
                candidates = [(a, b) for (a, b) in free_space
                              if (b-a) >= len(bytecode)]
                candidates = sorted(candidates,
                                    key=lambda x: (x[1]-x[0], x[0]))
                start, finish = candidates[0]
                free_space.remove((start, finish))
                new_start = start + len(bytecode)
                if new_start < finish:
                    free_space.add((new_start, finish))
                mpo.message_pointer_str = start.to_bytes(
                        length=3, byteorder='big')
                f.seek(start)
                f.write(bytecode)
            f.seek(0)
            mmo._data = f.read()
            f.close()


def decouple_fire_ryo():
    # This patches code in file 00a, which is compressed
    # It allows you to charge the Karakuri Camera without obtaining Fire Ryo.
    data = MapCategoryData.data
    if get_global_label() == 'MN64_JP':
        write_patch(data, 'patch_decouple_fire_ryo_00a.txt', noverify=True)
        write_patch(get_outfile(), 'patch_decouple_fire_ryo.txt')
    elif get_global_label() == 'MN64_EN':
        write_patch(data, 'patch_decouple_fire_ryo_00a_en.txt', noverify=True)
        write_patch(get_outfile(), 'patch_decouple_fire_ryo_en.txt')
    MapCategoryData.data = data


def do_flute_anywhere():
    if get_global_label() == 'MN64_JP':
        write_patch(get_outfile(), 'patch_flute_anywhere.txt')
    elif get_global_label() == 'MN64_EN':
        write_patch(get_outfile(), 'patch_flute_anywhere_en.txt')


def setup_save_warps(dr):
    WARP_DICT = {
        1:   0x15f,
        6:   0x169,
        7:   0x177,
        0xc: 0x179,
        0x10: 0xb7,
        }
    SaveWarpObject.create_properties()
    for index in sorted(WARP_DICT):
        swo = SaveWarpObject.get(index)
        assert swo.dest_room == WARP_DICT[index]
        swo.needs_update = True


def setup_dragon_warps(dr):
    DRAGON_ATLAS_INDEX = 0x10

    WARP_DICT = {
        0:   '1a1-001',  # Oedo Inn
        1:   '1b1-001',  # Kai Teahouse
        2:   '1d1-001',  # Oedo Castle becomes Goemon's House
        3:   '1a2-001',  # Zazen Inn
        4:   '1b3-001',  # Kii-Awaji Teahouse
        5:   '1a3-001',  # Folkypoke Inn
        6:   '1b4-001',  # Kompira Teahouse
        7:   '1b5-001',  # Iyo Teahouse
        9:   '1b6-001',  # Izumo Teahouse
        0xb: '1a4-001',  # Festival Village Inn
        #0xc: '1d4-001',  # Witch's Hut requires reorganizing dragon map
        0xd: '1a5-001',  # Gourmet Sub becomes Sogen Inn warp
        }

    INN_DICT = {
        '1d1-001': 0x90,
        '1a1-001': 0x8b,
        '1a2-001': 0x8c,
        '1a3-001': 0x8d,
        '1a4-001': 0x8e,
        '1a5-001': 0x93,
        }

    for index in range(0x8b, 0x90):
        MessagePointerObject.get(index).reallocate=True
    mpo = MessagePointerObject.get(0x8f)
    mpo.message = mpo.get(0x8f).message[-1:]
    mpo = MessagePointerObject.get(0x8b)
    if get_global_label() == 'MN64_JP':
        OEDO_WARP_ADDRESS = 0x8016209c
    elif get_global_label() == 'MN64_EN':
        OEDO_WARP_ADDRESS = 0x8015c8ac
    mpo.message.insert(0, (4, (OEDO_WARP_ADDRESS,)))
    mpo.message.insert(1, (9, (1,)))

    for mmo in MapMetaObject.every:
        if not mmo.is_room:
            continue
        for d in list(mmo.definitions):
            if d.actor_id in (0x2ee, 0x33d, 0x34e):
                d.remove()

    mmo = MapMetaObject.get(DRAGON_ATLAS_INDEX)
    if hasattr(mmo, '_data'):
        data = mmo._data
    else:
        data = mmo.get_decompressed()
    f = BytesIO(data)
    if get_global_label() == 'MN64_JP':
        write_patch(f, 'patch_dragon_atlas_010.txt', noverify=True)
    elif get_global_label() == 'MN64_EN':
        write_patch(f, 'patch_dragon_atlas_010_en.txt', noverify=True)
    f.seek(0)
    mmo._data = f.read()
    f.close()

    for dragon_index, signature in sorted(WARP_DICT.items()):
        room_exit = MapMetaObject.get_entity_by_signature(signature)
        node = dr.by_label(signature)
        edges = {e for e in node.edges if e.destination is not dr.root}
        if not edges:
            continue
        assert len(edges) == 1

        dwo = DragonWarpObject.get(dragon_index)
        for attr in ['dest_room', 'dest_x', 'dest_z', 'dest_y', 'direction']:
            value = room_exit.get_property_value(attr)
            value = value.to_bytes(length=2, byteorder='big')
            dwo_attr = f'{attr}_str'
            assert hasattr(dwo, dwo_attr)
            setattr(dwo, dwo_attr, value)
            dwo.needs_update = True

        if signature in INN_DICT:
            node_exit = list(node.edges)[0]
            pair_exit = MapMetaObject.get_entity_by_signature(
                    node_exit.destination.label)
            test = pair_exit.parent.debug_index
            actor_id = 0x31d
            attr = 'message'
            definition = room_exit.parent.add_new_definition(b'\x00' * 0x10)
            definition.set_main_property(actor_id)
            definition.set_property(attr, INN_DICT[signature])
            instance = room_exit.parent.EntityInstance(
                    b'\x00' * 0x14, room_exit.parent)
            instance.set_main_property(definition.index)
            instance.clean()
            room_exit.parent.spawn_groups[(-1,-1,-1)].append(instance)


def randomize_enemies():
    enemy_maps = [mmo for mmo in MapMetaObject.every
                  if mmo.is_room and mmo.enemies]
    enemy_files = []
    file_counts = []
    all_enemies = []
    for mmo in enemy_maps:
        if mmo.warp_index in mmo.NO_ENEMY_RANDOMIZE:
            continue
        files = {MapMetaObject.ENTITY_FILES[e.definition.actor_id]
                 for e in mmo.enemies}
        file_counts.append(len(files))
        enemy_files.extend(sorted(files))
        all_enemies.extend(mmo.enemies)
        for d in mmo.definitions:
            if 'enemies' in d.structure and d.get_property_value('enemies'):
                d.set_property('enemies', 0)
                if 'door_design' in d.structure:
                    d.set_property('door_design', 0)
    file_counts = sorted(file_counts)
    enemy_files = sorted(enemy_files)

    relative_z_data = defaultdict(list)
    for e in all_enemies:
        if not e.parent.exits:
            continue
        exits = sorted(e.parent.exits, key=lambda x: (e.get_distance(x),
                                                      x.signature))
        x = exits[0]
        ez = e.get_property_value('z')
        xz = x.get_property_value('z')
        if ez >= 0x8000:
            ez = (0x10000-ez) * -1
        if xz >= 0x8000:
            xz = (0x10000-xz) * -1
        relative_z = ez - xz
        relative_z_data[e.definition.actor_id].append(relative_z)

    mean_relative_z = {}
    for actor_id in relative_z_data:
        values = sorted(relative_z_data[actor_id])
        assert all(-0x8000 <= v <= 0x7fff for v in values)
        max_index = len(values) - 1
        if max_index % 2:
            index = max_index >> 1
            value = int(round((values[index] + values[index+1]) / 2))
        else:
            index = max_index >> 1
            value = values[index]
        mean_relative_z[actor_id] = value

    for mmo in enemy_maps:
        if mmo.warp_index in mmo.NO_ENEMY_RANDOMIZE:
            continue
        mmo.reseed('enemizer')
        old_files = {MapMetaObject.ENTITY_FILES[e.definition.actor_id]
                     for e in mmo.enemies}
        candidates = [n for n in file_counts if abs(n-len(old_files)) <= 1]
        new_file_count = random.choice(candidates)
        new_files = set()
        while len(new_files) < new_file_count:
            new_files.add(random.choice(enemy_files))
        new_files = sorted(new_files)
        enemy_candidates = [
                e for e in all_enemies if
                MapMetaObject.ENTITY_FILES[e.old_definition.old_actor_id]
                in new_files]
        enemy_definitions = [d for d in mmo.definitions if d.is_enemy]
        for enemy_def in enemy_definitions:
            chosen = random.choice(enemy_candidates)
            enemy_def.data = chosen.old_definition.old_data
            enemy_def.validate_data()
        if len(mmo.definitions) < 0x1e:
            chosen = random.choice(enemy_candidates)
            mmo.add_new_definition(chosen.old_definition.old_data)
        to_reassign = mmo.enemies
        for m in to_reassign:
            assert m.old_definition.old_actor_id != 0
        datas = set()
        for d in mmo.definitions:
            if not d.is_enemy:
                continue
            if d.data in datas:
                d.data = b'\x00' * 0x10
            datas.add(d.data)
        enemy_definitions = [d for d in mmo.definitions if d.is_enemy]
        lowest_z = min(m.get_property_value('z') for m in to_reassign)
        for m in to_reassign:
            assert m.old_definition.old_actor_id != 0
            chosen = random.choice(enemy_definitions)
            old_relative_z = mean_relative_z[m.old_definition.old_actor_id]
            m.set_main_property(chosen.index)
            new_relative_z = mean_relative_z[m.definition.actor_id]
            difference = new_relative_z - old_relative_z
            offset = random.randint(min(0, difference), max(0, difference))
            if abs(difference) >= 0x10:
                z = m.get_property_value('z')
                if z >= 0x8000:
                    z = (0x10000-z) * -1
                z += offset
                if z < 0:
                    z = 0x10000 + z
                z = max(z, lowest_z)
                m.set_property('z', z)
        while True:
            for d in mmo.definitions:
                if d.is_null:
                    d.remove()
                    break
            else:
                break


def randomize_doors():
    from randomtools.doorrouter import DoorRouter, DoorRouterException
    DEFAULT_CONFIG = 'mn64_settings.yaml'
    BACKUP_CONFIG = path.join(tblpath, 'default.mn64_settings.yaml')

    if 'MN64_CONFIG' in environ:
        config_filename = environ['MN64_CONFIG']
    else:
        print('A config file is required. Specify a filename.')
        config_filename = input(f'(Default: {DEFAULT_CONFIG})  ')
        if not config_filename.strip():
            config_filename = DEFAULT_CONFIG

    with open(config_filename) as f:
        config = yaml.safe_load(f.read())

    with open(BACKUP_CONFIG) as f:
        backup_config = yaml.safe_load(f.read())

    for key in sorted(backup_config):
        if key not in config:
            print(f'Using default value {backup_config[key]} for "{key}".')
            config[key] = backup_config[key]


    PEMOPEMO_LABEL = '14c-002'
    FINAL_ROOM_LABEL = '0c1-001'
    BIZEN_LOCK_LABEL = '143-009'
    MUSICAL_2_KEY_TRIGGER = '0bd-00f'
    FESTIVAL_WATERFALL_BLOCKER = '06f-00a'
    #SELF_LOOP_LABELS = ['14e-003', '14e-005']
    SELF_LOOP_LABELS = []

    MapMetaObject.set_pemopemo_destination(0xc1, 0xfe8a, 0xff60, 0x0, 0x100)

    if get_global_label() == 'MN64_JP':
        patch_filename = 'patch_initialize_variables.txt'
    elif get_global_label() == 'MN64_EN':
        patch_filename = 'patch_initialize_variables_en.txt'
    else:
        raise Exception('Unknown ROM version.')

    decouple_fire_ryo()

    parameters = {}
    definition_overrides = {}

    if config['enable_debug']:
        activate_code('debugmenu')

    if config['randomize_enemies']:
        activate_code('enemizer')

    #if 'enemizer' in get_activated_codes():
    #    definition_overrides['kill_ghosts'] = 'start'

    if config['completionist']:
        if 'goal' in definition_overrides:
            goal = definition_overrides['goal'] + '&everything'
        else:
            goal = 'pemopemo_god&everything'
        definition_overrides['goal'] = goal

    if config['all_warps']:
        if 'goal' in definition_overrides:
            goal = definition_overrides['goal'] + '&all_inns&all_teahouses'
        else:
            goal = 'pemopemo_god&all_inns&all_teahouses'
        definition_overrides['goal'] = goal

    if config['start_camera']:
        parameters['start_camera'] = 'c8'
        definition_overrides['camera'] = 'start'
    else:
        parameters['start_camera'] = '94'

    if config['start_minimaru']:
        parameters['start_minimaru'] = 'e8'
        definition_overrides['mini_ebisu'] = 'start'
    else:
        parameters['start_minimaru'] = '94'

    if config['start_flute']:
        parameters['start_yae'] = 'a0'
        parameters['start_flute'] = 'c0'
        definition_overrides['yae'] = 'start'
        definition_overrides['flute'] = 'start'
    else:
        parameters['start_yae'] = '94'
        parameters['start_flute'] = '94'

    if config['flute_anywhere']:
        definition_overrides['flute_anywhere'] = 'flute'
        do_flute_anywhere()

    if config['start_snow']:
        parameters['start_snow'] = '02 5c'
        definition_overrides['miracle_snow'] = 'start'
    else:
        parameters['start_snow'] = '00 94'

    if not config['ice_kunai_logic']:
        definition_overrides['ice_kunai_optional'] = 'start'

    if config['ryo_hover_logic']:
        definition_overrides['ryo_hover'] = 'start'

    if get_global_label() == 'MN64_JP' and config['jp_super_jump_logic']:
        definition_overrides['super_jump_jp'] = 'super_jump'

    write_patch(get_outfile(), patch_filename, parameters=parameters)

    if config['fix_bad_maps']:
        definition_overrides = fix_softlockable_rooms(definition_overrides)

    preset_connections = defaultdict(set)

    for mmo in MapMetaObject.sorted_rooms:
        if len(mmo.exits) == 1 and \
                config['fixed_singletons'] > random.random():
            x = mmo.exits[0]
            y = x.exit_pair
            if not (x and y):
                continue
            x = x.definition.signature
            y = y.definition.signature
            if FINAL_ROOM_LABEL not in {x, y}:
                assert x not in preset_connections
                assert y not in preset_connections
                preset_connections[x].add((y, frozenset()))
                preset_connections[y].add((x, frozenset()))
    preset_connections[FINAL_ROOM_LABEL].add((PEMOPEMO_LABEL, frozenset()))
    for label in SELF_LOOP_LABELS:
        assert label not in preset_connections
        preset_connections[label].add((label, frozenset()))

    if config['cluster_bgm']:
        def bgm_validator(node1, node2):
            a = MapMetaObject.get_entity_by_signature(node1.label)
            b = MapMetaObject.get_entity_by_signature(node2.label)
            if a.parent.matches_bgm(b.parent):
                return True
            return not (a.destination_has_same_bgm or
                        b.destination_has_same_bgm)
    else:
        def bgm_validator(node1, node2):
            return True

    if 'seed' not in config:
        config['seed'] = get_seed()

    print('\nNow beginning the maze generation process. This can take around\n'
          '20 minutes depending on your settings and your system specs.\n'
          'While you wait, check out ko-fi.com/abyssonym for additional\n'
          'dev notes and exclusive content!\n')
    dr = DoorRouter(config=config, preset_connections=preset_connections,
                    strict_validator=None, lenient_validator=bgm_validator,
                    definition_overrides=definition_overrides)
    dr.build_graph()
    random.seed(dr.seed)
    setup_save_warps(dr)
    setup_dragon_warps(dr)
    random.seed(dr.seed)

    def label_to_mmo(label):
        return MapMetaObject.get_by_warp_index(int(label.split('-')[0], 0x10))

    # Set exit destinations
    for e in sorted(dr.all_edges):
        if not (e.generated or e.source.label == FINAL_ROOM_LABEL):
            continue
        source = MapMetaObject.get_entity_by_signature(e.source.label)
        dest = MapMetaObject.get_entity_by_signature(e.destination.label)
        dest = dest.instances[0]
        dest_source = dest.exit_pair.definition
        for attr in ('dest_room', 'dest_x', 'dest_z', 'dest_y', 'direction'):
            value = dest_source.get_property_value(attr, old=True)
            source.set_property(attr, value)

    # Clear unused exits
    for n in sorted(dr.connectable):
        if n.label in preset_connections:
            continue
        if any(e.generated for e in n.edges):
            continue
        source = MapMetaObject.get_entity_by_signature(n.label)
        if not source.is_exit:
            continue
        for x in source.instances:
            x.spawn_door_blocker()
        if source.door is not None:
            if source.door.is_lock:
                source.door.become_regular_door()
            source.door.remove()
        source.remove()

    silver_cats = set()
    gold_cats = set()
    for mmo in MapMetaObject.sorted_rooms:
        for e in mmo.definitions:
            if e.is_lock:
                if e.signature == BIZEN_LOCK_LABEL:
                    continue
                e.become_regular_door()
            if e.is_key or e.is_elly_fant or e.is_mr_arrow:
                e.become_gold_dango()
            if e.is_silver_cat:
                silver_cats.add(e.get_property_value('flag'))
            if e.is_gold_cat:
                gold_cats.add(e.get_property_value('flag'))

    key_assignments = {}
    num_key_trials = int(dr.config['randomize_keys'])
    if num_key_trials:
        trials = {}
        trial_types = {}
        trial_scores = {}
        dr.commit()
        counter = 0
        while True:
            print(f'Creating a potential key chain. '
                  f'({counter+1}/{num_key_trials})')
            random.seed(dr.seed+counter)
            try:
                trial_key = f'lock{counter}'
                trials[trial_key], trial_types[trial_key] = generate_locks(dr)
                key_assignments = trials[trial_key]
                keys_and_locks = key_assignments.keys() | \
                        key_assignments.values()
                goal_guaranteed = {n for g in dr.goal_nodes
                                   for n in g.guaranteed}
                goal_trial = goal_guaranteed & keys_and_locks
                score = len(goal_trial)
                trial_scores[trial_key] = score
                dr.commit(trial_key)
            except DoorRouterException:
                print(f'Error: Generation failed.')
            dr.rollback()
            counter += 1
            if trials and counter >= num_key_trials:
                break

        trial_keys = sorted(trials,
                key=lambda tk: (trial_scores[tk] * len(trials[tk]),
                                trial_scores[tk], len(trials[tk]), tk))
        trial_key = trial_keys[-1]
        dr.rollback(trial_key)
        dr.commit()
        key_assignments = trials[trial_key]
        key_type_pairs = trial_types[trial_key]

        num_available = (len(MapMetaObject.available_memory_flags) >> 1) - 1
        random.seed(dr.seed)
        while len(key_assignments) >= num_available:
            counted = Counter(key_type_pairs.values()).most_common()
            highest = counted[0][1]
            candidates = [key_type for (key_type, count) in counted
                          if count == highest]
            chosen = random.choice(sorted(candidates))
            candidates = {lock for (lock, key_type) in key_type_pairs.items()
                          if key_type == chosen}
            chosen = random.choice(sorted(candidates))
            del(key_type_pairs[chosen])
            chosen = [k for (k, v) in key_assignments.items() if v == chosen]
            for c in chosen:
                del(key_assignments[c])

        for lock, key in key_assignments.items():
            key_type = key_type_pairs[key]
            lock = MapMetaObject.get_entity_by_signature(lock.label)
            assert lock.is_exit
            assert lock.door
            key = MapMetaObject.get_entity_by_signature(key.label)
            assert key.is_pickup
            key.become_key(key_type=key_type)
            lock.door.become_locked_door(key=key)

            # SIRO 54 - Game crashes if locked door has x = 0163
            for i in lock.door.instances:
                i.set_property('rotx', i.get_property_value('rotx') | 1)

    random.seed(dr.seed)
    solutions = dr.generate_solutions()
    s = ''
    previous_line = None
    for node, solpath in solutions:
        warp_index = node.label.split('-')[0]
        extra = None
        if node in key_assignments.values():
            extra = '{0} Key'.format(
                    MapMetaObject.get_entity_by_signature(
                        node.label).get_pretty_value('key_type'))
        mmo = label_to_mmo(node.label)
        if extra is None:
            s += f'\n{warp_index} {mmo.room_name}\n'
        else:
            s += f'\n{warp_index} {mmo.room_name} **{extra}**\n'
        nodes = [p.destination for p in solpath]
        previous_line = None
        pathlines = []
        for n in nodes:
            mmo = label_to_mmo(n.label)
            line = f'  {mmo.debug_index:10} {mmo.room_name}'
            if n in key_assignments.keys() and n is not node:
                line += ' **{0} Lock**'.format(
                        MapMetaObject.get_entity_by_signature(
                            n.label).door.get_pretty_value('key_type'))
            if (not pathlines) or line != pathlines[-1]:
                pathlines.append(line)
            if len(pathlines) >= 2:
                a, b = pathlines[-2], pathlines[-1]
                if a.startswith(b):
                    pathlines = pathlines[:-2] + [a]
                elif b.startswith(a):
                    pathlines = pathlines[:-2] + [b]
        s += '\n'.join(pathlines) + '\n'
    s = s.strip()
    solution_filename = f'{get_outfile()}.spoiler.txt'
    timestamp = datetime.strftime(datetime.now(), '%Y%m%d%H')
    header = (f'MN64 Randomizer v{VERSION}\n'
              f'Seed        {get_seed()}\n'
              f'Timestamp   {timestamp}\n')
    s = f'{header.strip()}\n\n{dr.description}\n\n{s}'
    with open(solution_filename, 'w+') as f:
        f.write(s)
    f = get_open_file(get_outfile())
    f.seek(addresses.seed_info_address)
    f.write(s.encode('ascii'))

    m2key = MapMetaObject.get_entity_by_signature(MUSICAL_2_KEY_TRIGGER)
    old_flag = m2key.get_property_value('key_index', old=True)
    if 'flag' in m2key.structure:
        flag = m2key.get_property_value('flag')
    elif 'key_index' in m2key.structure:
        flag = m2key.get_property_value('key_index')
    else:
        flag = MapMetaObject.acquire_memory_flag()
        m2key.become_surprise_pack(flag)
        flag = m2key.get_property_value('flag')

    for e in m2key.parent.definitions:
        if 'flag' in e.structure and e.get_property_value('flag') == old_flag:
            e.set_property('flag', flag)

    pickups = set()
    if dr.config['randomize_pickups']:
        for mmo in MapMetaObject.sorted_rooms:
            for e in mmo.definitions:
                if e is m2key:
                    continue
                if e.is_pot:
                    e.randomize_pot()
                if e.is_cat or e.is_surprise_pack:
                    e.become_gold_dango()
                if e.is_pickup and not e.is_key:
                    assert e.is_gold_dango
                    node = dr.get_by_label(e.signature)
                    if node and node.rooted:
                        pickups.add(e)

        pickups = sorted(pickups)
        MapMetaObject.available_memory_flags -= (silver_cats | gold_cats)
        num_entities = min(len(gold_cats), len(pickups))
        if num_entities < len(gold_cats):
            print('WARNING: Unable to allocate all golden cat dolls.')
        gold_cat_entities = random.sample(pickups, num_entities)
        pickups = sorted(set(pickups) - set(gold_cat_entities))
        for e, flag in zip(gold_cat_entities, gold_cats):
            e.become_gold_cat(flag)

        num_entities = min(len(silver_cats), len(pickups))
        if num_entities < len(silver_cats):
            print('WARNING: Unable to allocate all silver cat dolls.')
        silver_cat_entities = random.sample(pickups, num_entities)
        pickups = sorted(set(pickups) - set(silver_cat_entities))
        for e, flag in zip(silver_cat_entities, silver_cats):
            e.become_silver_cat(flag)

        for e in pickups:
            e.become_random_pickup()

    festival_blocker = MapMetaObject.get_entity_by_signature(
            FESTIVAL_WATERFALL_BLOCKER)
    festival_blocker.remove()

    random.seed(dr.seed)
    add_roommates()


def generate_locks(dr):
    BANNED_DOORS = {'15e-002', '1b8-001', '1b9-001',
                    '028-001', '049-001', '071-001', '09d-001',
                    '137-002', '138-002', '139-002',
                    '14c-002', '0c1-001', '143-008',
                    '039-003', '03b-001', '040-001',
                    '02f-003', '16e-002',}
    preliminary_lockable = set()
    preliminary_keyable = {
            n for n in dr.rooted if '-x' not in n.label and
            MapMetaObject.get_entity_by_signature(n.label).is_pickup}
    for i, edge in enumerate(dr.all_edges):
        if edge.source.label in BANNED_DOORS:
            continue
        if '-x' in edge.source.label:
            continue
        if '-x' in edge.destination.label:
            continue
        node = edge.source
        x = MapMetaObject.get_entity_by_signature(node.label)
        if not x.is_exit:
            continue
        if not x.door:
            continue
        if x.door.actor_id not in MapMetaObject.EntityDefinition.DOOR_DESIGNS:
            continue
        if not MapMetaObject.EntityDefinition.DOOR_DESIGNS[x.door.actor_id]:
            continue
        x2 = MapMetaObject.get_entity_by_signature(edge.destination.label)
        if not x2.is_exit:
            continue
        if x.parent is x2.parent and not edge.generated:
            continue
        if not (edge.source.rooted and edge.destination.rooted):
            continue
        preliminary_lockable.add(edge)

    requirement_nodes = {n for n in dr.reachable_from_root if n.required_nodes}
    used_key_locations = set()
    used_lock_locations = set()
    lock_key_pairs = {}
    key_type_pairs = {}
    for key_type in ['Silver', 'Gold', 'Diamond']:
        print(f'Generating {key_type.lower()} keys...')
        dr.commit(key_type)
        lockable = set()
        for e in preliminary_lockable:
            if e in used_lock_locations:
                continue
            orphans = e.get_guaranteed_orphanable()
            if not orphans:
                continue
            nonorphans = dr.reachable_from_root - orphans
            for n in nonorphans:
                if n.required_nodes & orphans:
                    break
            else:
                lockable.add(e)

        hierarchy = {}
        reverse_hierarchy = defaultdict(set)
        for e in preliminary_lockable:
            orphans = e.get_guaranteed_orphanable()
            orphan_edges = {e2 for e2 in preliminary_lockable
                            if e2.source in orphans}
            hierarchy[e] = orphan_edges
            for e2 in orphan_edges:
                assert e2.rank > e.rank
                reverse_hierarchy[e2].add(e)

        valid_edges = set(lockable)
        bad_starters = set()
        key_chain = []
        keyable_dict = {}
        while True:
            valid_edges = valid_edges - bad_starters
            starters = {e for e in lockable & valid_edges
                        if e not in key_chain and
                        len(reverse_hierarchy[e] & valid_edges) == 0}
            starters = starters - bad_starters
            if key_chain:
                starters &= hierarchy[key_chain[-1]]
            if not starters:
                break
            good_starters = {e for e in starters
                             if len(hierarchy[e] & valid_edges) > 0}
            if good_starters and key_type in ['Silver']:
                starters &= good_starters
            orphan_pool = sorted(o for s in starters
                                 for o in s.get_guaranteed_orphanable())
            goal_pool = dr.goal_nodes & set(orphan_pool)
            keyable_pool = set(orphan_pool) & \
                    (preliminary_keyable | dr.conditional_nodes)
            if goal_pool and key_type in ['Gold', 'Diamond']:
                orphan_pool = [o for o in orphan_pool if o in goal_pool]
            elif keyable_pool:
                orphan_pool = [o for o in orphan_pool if o in keyable_pool]
            good_orphan_pool = sorted(o for s in good_starters
                                      for o in s.get_guaranteed_orphanable()
                                      if o in orphan_pool)
            if good_orphan_pool and key_type in ['Silver', 'Gold']:
                starters = good_starters
                orphan_pool = good_orphan_pool
            orphan = random.choice(sorted(orphan_pool))
            starters = {s for s in starters if
                        orphan in s.get_guaranteed_orphanable()}
            assert starters
            starters = sorted(starters, key=lambda e: str(e))
            chosen = random.choice(starters)
            chosen_keyable = preliminary_keyable - \
                    (chosen.get_guaranteed_orphanable() | used_key_locations)
            for c in list(chosen_keyable):
                c.get_guaranteed_reachable_only(seek_nodes={chosen.source})
                if not any(n.orphanless for n in c.guar_to[chosen.source]):
                    continue
                c.get_guaranteed_reachable_only()
                if any(n.orphanless for n in c.guar_to[chosen.source]):
                    chosen_keyable.remove(c)
            if not chosen_keyable:
                bad_starters.add(chosen)
                continue
            rfc = chosen.source.get_naive_avoid_reachable(
                    avoid_edges={chosen}, seek_nodes={dr.root})
            if dr.root not in rfc:
                bad_starters.add(chosen)
                continue

            orphans = chosen.get_guaranteed_orphanable()
            nonorphans = dr.reachable_from_root - orphans
            requirements_pass = True
            for n in requirement_nodes & nonorphans:
                rs = n.required_nodes & nonorphans
                rs = {r for r in rs
                      if r.rank > min(n.rank, chosen.destination.rank)}
                if not rs:
                    continue
                for r in rs:
                    solpath = r.get_shortest_path(avoid_nodes={n},
                                                  avoid_edges={chosen})
                    if not solpath:
                        requirements_pass = False
                        break

            if not requirements_pass:
                bad_starters.add(chosen)
                continue

            orphans = chosen.get_guaranteed_orphanable()
            assert orphans and rfc and not rfc & orphans
            valid_edges &= hierarchy[chosen]
            key_chain.append(chosen)
            keyable_dict[chosen] = chosen_keyable

        for (a, b) in zip(key_chain, key_chain[1:]):
            assert b in hierarchy[a]
            assert a not in hierarchy[b]
            assert hierarchy[b] < hierarchy[a]

        while True:
            if not key_chain:
                break
            keyable_ranges = {}
            keyable_ranges[key_chain[0]] = keyable_dict[key_chain[0]]
            candidates = set()
            for (a, b) in zip(key_chain, key_chain[1:]):
                keyable_ranges[b] = keyable_dict[b] - keyable_dict[a]
                threshold = random.choice([0, 1])
                if len(keyable_ranges[b]) <= threshold:
                    candidates |= {a, b}
            if not candidates:
                break
            chosen = random.choice(sorted(candidates))
            key_chain.remove(chosen)

        for to_lock in key_chain:
            to_key = random.choice(sorted(keyable_ranges[to_lock]))
            to_lock.remove()
            to_lock.source.add_edge(
                    to_lock.destination, condition=frozenset({to_key.label}),
                    procedural=to_lock.generated)
            used_key_locations.add(to_key)
            used_lock_locations.add(to_lock)
            assert to_lock.source not in lock_key_pairs
            assert to_key not in lock_key_pairs.values()
            lock_key_pairs[to_lock.source] = to_key
            key_type_pairs[to_key] = key_type

        to_cleanup = set()
        original_key_chain_length = len(key_chain)
        while True:
            try:
                dr.clear_rooted_cache()
                assert not (dr.reachable_from_root - dr.root_reachable_from)
                assert dr.goal_reached
                dr.verify()
                break
            except Exception:
                #print(f'Generation failure. Attempting to correct. '
                #      f'({len(key_chain)}/{original_key_chain_length})')
                print(f'Generation failure. Attempting to correct...')
                to_lock = random.choice(key_chain)
                key_chain.remove(to_lock)
                to_key = lock_key_pairs[to_lock.source]
                locked = [e for e in to_lock.source.edges
                          if e.destination is to_lock.destination
                          and e.true_condition == {to_key}][0]
                to_cleanup.add(locked)
                to_lock.source.add_edge(
                        to_lock.destination, procedural=to_lock.generated)
                del(lock_key_pairs[to_lock.source])
                del(key_type_pairs[to_key])
                used_lock_locations.remove(to_lock)
                used_key_locations.remove(to_key)
        for locked in to_cleanup:
            locked.remove()
        dr.rooted

    return lock_key_pairs, key_type_pairs


def fix_softlockable_rooms(definition_overrides):
    DRUM_PLATFORM_ID = 0x1a1
    mmo = MapMetaObject.get_by_warp_index(0x91)
    definition = mmo.add_new_definition(b'\x00' * 0x10)
    definition.set_main_property(DRUM_PLATFORM_ID)
    instance = mmo.EntityInstance(b'\x00' * 0x14, mmo)
    instance.set_main_property(definition.index)
    instance.clean()
    x, y, z = 0xc4, 0xffd8, 0xff90
    instance.set_property('x', x)
    instance.set_property('y', y)
    instance.set_property('z', z)
    mmo.spawn_groups[(-1,-1,-1)].append(instance)
    definition_overrides['softlock_091'] = 'start'

    mmo = MapMetaObject.get_by_warp_index(0x142)
    SHORT_LADDER_ID = 0x33b
    definition = [d for d in mmo.definitions
                  if d.actor_id == SHORT_LADDER_ID][0]
    instance = mmo.EntityInstance(b'\x00' * 0x14, mmo)
    instance.set_main_property(definition.index)
    instance.clean()
    x, y, z = 0x9f, 0xff3c, 0xff9c
    instance.set_property('x', x)
    instance.set_property('y', y)
    instance.set_property('z', z)
    mmo.spawn_groups[(-1,-1,-1)].append(instance)

    LONG_LADDER_ID = 0x33c
    definition = mmo.add_new_definition(b'\x00' * 0x10)
    definition.set_main_property(LONG_LADDER_ID)
    instance = mmo.EntityInstance(b'\x00' * 0x14, mmo)
    instance.set_main_property(definition.index)
    instance.clean()
    x, y, z = 0x9f, 0xfebc, 0x14
    instance.set_property('x', x)
    instance.set_property('y', y)
    instance.set_property('z', z)
    mmo.spawn_groups[(-1,-1,-1)].append(instance)
    definition_overrides['softlock_142'] = 'start'

    return definition_overrides


def add_roommates():
    NPC_FILES = [0x1a]
    candidates = {c for c in MapMetaObject.ENTITY_FILES
                  if MapMetaObject.ENTITY_FILES[c] in NPC_FILES
                  and c in MapMetaObject.ENTITY_STRUCTURES}
    mmo = MapMetaObject.get_by_warp_index(0x1d1)

    x_values = [0xffe8, 0xfff4, 0, 0xc]
    chosen = [random.choice(sorted(candidates)) for x in x_values]
    while chosen:
        actor_id = chosen.pop()
        definition = mmo.add_new_definition(b'\x00' * 0x10)
        definition.set_main_property(actor_id)
        instance = mmo.EntityInstance(b'\x00' * 0x14, mmo)
        instance.set_main_property(definition.index)
        instance.clean()
        instance.set_property('x', x_values.pop())
        instance.set_property('y', 0xfff0)
        instance.set_property('z', 0xfff0)
        mmo.spawn_groups[(-1,-1,-1)].append(instance)


def export_data():
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
        export_filename = environ['MN64_EXPORT']
    else:
        export_filename = f'{get_outfile()}.export.txt'
    print(f'EXPORTING to {export_filename}')
    with open(export_filename, 'w+') as f:
        s =  (f'# Seed:   {get_seed()}\n')
        s += (f'# Flags:  {get_flags()}\n')
        done_codes = ','.join(get_activated_codes())
        s += (f'# Codes:  {done_codes}\n')
        s += (f'# Import: {import_filename}\n')
        f.write(s + '\n')
        for mmo in MapMetaObject.sorted_rooms:
            f.write(str(mmo) + '\n\n')


def write_abridged_metadata():
    timestamp = datetime.strftime(datetime.now(), '%Y%m%d%H')
    header = (f'MN64 Randomizer v{VERSION}\n'
              f'Seed        {get_seed()}\n'
              f'Timestamp   {timestamp}\n')
    f = get_open_file(get_outfile())
    f.seek(addresses.seed_info_address)
    f.write(header.strip().encode('ascii'))


if __name__ == '__main__':
    try:
        print('You are using the Ancient Cave Starring Goemon '
              'randomizer version %s.' % VERSION)

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]

        codes = {
            'export': ['export'],
            'import': ['import'],
            'norandom': ['norandom'],
            'enemizer': ['enemizer'],
            'debugmenu': ['debugmenu'],
        }

        run_interface(ALL_OBJECTS, snes=False, n64=True, codes=codes,
                      custom_degree=False, custom_difficulty=False)
        for code in sorted(get_activated_codes()):
            print('Code "%s" activated.' % code)

        import_filename = None
        if 'import' in get_activated_codes():
            if 'MN64_IMPORT' in environ:
                import_filename = environ['MN64_IMPORT']
            else:
                import_filename = input('Import from filename: ')
            if not import_filename.strip():
                import_filename = f'{get_sourcefile()}.import.txt'
            print(f'IMPORTING from {import_filename}')
            MapMetaObject.import_from_file(import_filename)

        if 'norandom' not in get_activated_codes():
            randomize_doors()
        else:
            write_abridged_metadata()

        for mmo in MapMetaObject.every:
            if mmo.data_has_changed:
                if mmo.room_name:
                    name = f'ROOM {mmo.warp_index:0>3X} {mmo.room_name}'
                else:
                    name = f'FILE {mmo.index:0>3X}'
                if VERBOSE or DEBUG_MODE:
                    print('Updated:', name)

        if 'enemizer' in get_activated_codes():
            randomize_enemies()

        if 'debugmenu' in get_activated_codes():
            if get_global_label() == 'MN64_JP':
                patch_filename = 'patch_debug_menu.txt'
            elif get_global_label() == 'MN64_EN':
                patch_filename = 'patch_debug_menu_en.txt'
            else:
                raise Exception('Unknown ROM version.')
            write_patch(get_outfile(), patch_filename)

        decouple_fire_ryo()

        modified = ('import' in get_activated_codes() or
                    'enemizer' in get_activated_codes() or
                    'norandom' not in get_activated_codes())

        if modified:
            clean_and_write(ALL_OBJECTS)
            if 'export' in get_activated_codes():
                export_data()
        else:
            if 'export' in get_activated_codes():
                print('No modifications made; generating clean export.')
                export_data()
                finish_interface()
                exit(0)
            clean_and_write(ALL_OBJECTS)

        checksum(get_open_file(get_outfile()))
        finish_interface()

    except Exception:
        print('ERROR: %s' % format_exc())
        input('Press Enter to close this program. ')
