from sys import argv

# pointer table in RAM dump
BASE_POINTER_TABLE = 0x235fe8

reverse_lookup = {}
with open(argv[1], 'r+b') as f:
    for room_index in range(1, 0x325):
        f.seek(BASE_POINTER_TABLE + ((room_index-1) * 4))
        next_pointer = int.from_bytes(f.read(4), byteorder='big') & 0x7fffffff
        f.seek(next_pointer + 0x18)
        next_pointer = int.from_bytes(f.read(4), byteorder='big') & 0x7fffffff
        f.seek(next_pointer + 0x12)
        offset = int.from_bytes(f.read(2), byteorder='big')
        next_pointer = 0x230000 | offset
        f.seek(next_pointer)
        indexes = []
        while True:
            value = int.from_bytes(f.read(2), byteorder='big')
            if value == 0:
                break
            indexes.append(value)
            if 0x335 <= value <= 0x481:
                if value in reverse_lookup:
                    assert value == 0x335
                    assert reverse_lookup[value] == 0x195
                    assert room_index == 0x1d3
                    del(reverse_lookup[value])
                reverse_lookup[value] = room_index
        indexes = ','.join([f'{v:0>3x}'.format(v) for v in indexes])
        if indexes:
            print(f'{room_index:0>3x}:  {indexes}')

print()
print('MAPPING')
for reverse_index in sorted(reverse_lookup):
    print(f'{reverse_lookup[reverse_index]:0>3x} {reverse_index:0>3x}')
print()
print('REVERSE MAPPING')
for reverse_index in sorted(reverse_lookup):
    print(f'{reverse_index:0>3x} {reverse_lookup[reverse_index]:0>3x}')
