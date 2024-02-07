from sys import argv
from textwrap import wrap
try:
    from colorama import Fore, Style
except ImportError:
    pass
from subprocess import call
from os import listdir


DEBUG = False
if DEBUG:
    logfile = open('decompress_debug.log', 'w+')


def log(msg):
    if DEBUG:
        logfile.write(str(msg) + '\n')


if 'lzkn64' in listdir('.'):
    VERIFY = True
else:
    VERIFY = False


OPTIMIZE_ZEROES = False


TMP_INFILE = 'tmp.in'
TMP_OUTFILE = 'tmp.out'
TMP_TESTFILE = 'tmp.test'

def initialize_temp():
    call(['truncate', '--size', '0', TMP_INFILE])
    call(['truncate', '--size', '0', TMP_OUTFILE])
    call(['truncate', '--size', '0', TMP_TESTFILE])


def hexify(s):
    result = []
    while s:
        w = s[:4]
        s = s[4:]
        w = ' '.join('{0:0>2x}'.format(c) for c in w)
        result.append(w)
    return ' '.join(result)


def checksum(outfile):
    # checksum algorithm ported from n64crc.c by Sterbenz & Parasyte & spinout
    mask = 0xffffffff

    def rol(i, b):
        return ((i << b) | (i >> (32-b))) & mask

    seed = 0xF8CA4DDC
    t1 = t2 = t3 = t4 = t5 = t6 = seed
    outfile.seek(0x1000)
    for i in range(0x1000, 0x101000, 4):
        assert i == outfile.tell()
        d = int.from_bytes(outfile.read(4), byteorder='big')
        if (t6 + d) & mask < t6:
            t4 = (t4 + 1) & mask
        t6 = (t6 + d) & mask
        t3 ^= d
        r = rol(d, (d & 0x1f))
        t5 = (t5 + r) & mask
        if t2 > d:
            t2 ^= r
        else:
            t2 ^= (t6 ^ d)
        t1 = (t1 + (t5 ^ d)) & mask
    crc1 = (t6 ^ t4 ^ t3)
    crc2 = (t5 ^ t2 ^ t1)
    data = ((crc1 << 32) | crc2).to_bytes(length=8, byteorder='big')
    outfile.seek(0x10)
    outfile.write(data)


def decompress_lzkn64(data):
    initialize_temp()
    with open(TMP_INFILE, 'r+b') as f:
        f.write(data)
    cmd = ['./lzkn64', '-d', TMP_INFILE, TMP_OUTFILE]
    call(cmd)
    with open(TMP_OUTFILE, 'r+b') as f:
        data = f.read()
    return data


def recompress_lzkn64(data):
    initialize_temp()
    with open(TMP_INFILE, 'r+b') as f:
        f.write(data)
    cmd = ['./lzkn64', '-c', TMP_INFILE, TMP_OUTFILE]
    call(cmd)
    with open(TMP_OUTFILE, 'r+b') as f:
        data = f.read()
    return data


def decompress(source_data, validation_data=None):
    feed = source_data
    decomp = b''
    good_comp_length = 0
    good_decomp_length = 0
    try:
        while True:
            if not feed:
                break
            opcode, feed = feed[0], feed[1:]
            if opcode == 0 and not feed:
                decomp += b'\x00\x00'
                break
            if opcode == 0xff:
                length, feed = feed[0], feed[1:]
                decomp += b'\x00' * (length+2)
            elif opcode >> 4 in {0x8, 0x9, 0xa, 0xb}:
                length = opcode & 0x7f
                segment, feed = feed[:length], feed[length:]
                if len(segment) != length:
                    raise Exception('Ran out of data. (2)')
                decomp += segment
            elif opcode >> 4 in {0xc, 0xd}:
                length = (opcode & 0x1f) + 2
                segment, feed = feed[:1], feed[1:]
                decomp += (segment * length)
            elif opcode >> 4 in {0xe, 0xf}:
                length = opcode & 0x1f
                decomp += b'\x00' * (length+2)
            elif 0 <= (opcode >> 4) <= 7:
                lookback, feed = feed[0], feed[1:]
                length = (opcode >> 2) + 2
                lookback |= ((opcode & 0b11) << 8)
                if lookback == 0:
                    segment = b'\x00'
                else:
                    segment = (decomp[-lookback:])[:length]
                while len(segment) < length:
                    segment = segment + segment
                segment = segment[:length]
                if len(segment) != length:
                    raise Exception('Ran out of data. (3)')
                decomp += segment
            else:
                raise Exception('Unknown opcode: {0:0>2x}'.format(opcode))
            if validation_data and not validation_data.startswith(decomp):
                raise Exception('Decompression does not match.')
            else:
                good_comp_length = len(source_data) - len(feed)
                good_decomp_length = len(decomp)
    except Exception as error:
        print(error.args[0])
        print()
        error_comp_length = (len(source_data) - len(feed)) - good_comp_length
        consumed_comp_length = good_comp_length + error_comp_length
        error_decomp_length = len(decomp) - good_decomp_length
        good_comp = source_data[:good_comp_length]
        bad_comp = source_data[good_comp_length:consumed_comp_length]
        extra_comp = source_data[consumed_comp_length:consumed_comp_length+4]
        print(f'{Fore.GREEN}{hexify(good_comp)} {Fore.RED}{hexify(bad_comp)} {Style.RESET_ALL}{hexify(extra_comp)}')
        print()
        good_decomp = decomp[:good_decomp_length]
        bad_decomp = decomp[good_decomp_length:]
        extra_decomp = b''
        print(f'{Fore.GREEN}{hexify(good_decomp)} {Fore.RED}{hexify(bad_decomp)} {Style.RESET_ALL}{hexify(extra_decomp)}')
        print()
        if validation_data:
            good_decomp = validation_data[:good_decomp_length]
            bad_decomp = validation_data[good_decomp_length:len(decomp)]
            extra_decomp = validation_data[len(decomp):len(decomp)+4]
            print(f'{Fore.GREEN}{hexify(good_decomp)} {Fore.RED}{hexify(bad_decomp)} {Style.RESET_ALL}{hexify(extra_decomp)}')
        raise Exception('Decompression failed.')

    return decomp


def decompress_from_file(source_file, offset,
                         validation_data=None, verify=None):
    if verify is None:
        verify = VERIFY

    source_file.seek(offset)
    length = int.from_bytes(source_file.read(4), byteorder='big')
    assert length <= 0xffffff
    source_file.seek(offset)
    source_data = source_file.read(length)

    if verify:
        verify_data = decompress_lzkn64(source_data)
        assert verify_data
        decomp = decompress(source_data[4:], verify_data)
        assert decomp == verify_data
    else:
        decomp = decompress(source_data[4:], validation_data)
    return decomp


def recomp_match_search1(buffer_position, file_buffer):
    # original algorithm in Fluvian's implementation
    WINDOW_SIZE = 0x3ff
    COPY_SIZE = 0x21
    sliding_window_match_position = -1
    sliding_window_match_size = 0
    sliding_window_maximum_offset = max(0, buffer_position-WINDOW_SIZE)
    buffer_size = len(file_buffer)
    sliding_window_maximum_length = min(
            COPY_SIZE, ((buffer_size-1) - buffer_position))

    # Go backwards in the buffer, is there a matching value?
    # If yes, search forward and check for more matching values in a loop.
    # If no, go further back and repeat.
    for search_position in range(
            buffer_position-1, sliding_window_maximum_offset-1, -1):
        matching_sequence_size = 0
        while (file_buffer[search_position+matching_sequence_size] ==
                file_buffer[buffer_position+matching_sequence_size]):
            matching_sequence_size += 1
            if matching_sequence_size >= sliding_window_maximum_length:
                break
        # Once we find a match or a match that is bigger than the match
        # before it, we save its position and length.
        if matching_sequence_size > sliding_window_match_size:
            sliding_window_match_position = search_position
            sliding_window_match_size = matching_sequence_size
    return sliding_window_match_position, sliding_window_match_size

def recomp_match_search2(buffer_position, file_buffer, optimize=True):
    # slightly altered version with same output, optimized for Python
    WINDOW_SIZE = 0x3ff
    COPY_SIZE = 0x21
    sliding_window_match_position = -1
    sliding_window_match_size = 0
    sliding_window_maximum_offset = max(0, buffer_position-WINDOW_SIZE)
    buffer_size = len(file_buffer)
    sliding_window_maximum_length = min(
            COPY_SIZE, ((buffer_size-1) - buffer_position))

    available_lookback = \
            file_buffer[sliding_window_maximum_offset:buffer_position]
    lookback_length = len(available_lookback)
    for segment_length in range(sliding_window_maximum_length, 2, -1):
        segment = file_buffer[buffer_position:buffer_position+segment_length]
        if optimize:
            for subsegment_length in range(
                    min(segment_length, lookback_length), 0, -1):
                if not segment.startswith(
                        available_lookback[-subsegment_length:]):
                    continue
                subsegment = segment[:subsegment_length]
                test = subsegment * (int(len(segment) / len(subsegment))+1)
                if test.startswith(segment):
                    return buffer_position-subsegment_length, segment_length
        try:
            index = available_lookback.index(segment)
            return (index+sliding_window_maximum_offset), segment_length
        except ValueError:
            pass
    return -1, 0

def recomp_match_search3(buffer_position, file_buffer):
    # very fast version that sacrifices some compression for speed
    WINDOW_SIZE = 0x3ff
    COPY_SIZE = 0x21
    sliding_window_match_position = -1
    sliding_window_match_size = 0
    sliding_window_maximum_offset = max(0, buffer_position-WINDOW_SIZE)
    buffer_size = len(file_buffer)
    sliding_window_maximum_length = min(
            COPY_SIZE, ((buffer_size-1) - buffer_position))

    available_lookback = \
            file_buffer[sliding_window_maximum_offset:buffer_position]
    lookback_length = len(available_lookback)
    best_index = -1
    best_length = 0
    for segment_length in range(2, sliding_window_maximum_length+1, 1):
        segment = file_buffer[buffer_position:buffer_position+segment_length]
        try:
            best_index = available_lookback.index(segment)
            best_length = segment_length
        except ValueError:
            break
    return (best_index+sliding_window_maximum_offset), best_length


def recompress(decomp, verify=None):
    # ported from lzkn64.c by Fluvian
    if verify is None:
        verify = VERIFY
    MODE_WINDOW_COPY = 0
    MODE_RAW_COPY = 0x80
    MODE_RLE_WRITE_A = 0xC0
    MODE_RLE_WRITE_B = 0xE0
    MODE_RLE_WRITE_C = 0xFF

    WINDOW_SIZE = 0x3ff
    COPY_SIZE = 0x21
    RLE_SIZE = 0x101

    file_buffer = decomp
    buffer_size = len(file_buffer)
    write_buffer = [0] * (buffer_size*2)

    buffer_position = 0
    write_position = 4
    buffer_last_copy_position = 0

    while buffer_position < buffer_size:
        sliding_window_maximum_length = min(
                COPY_SIZE, ((buffer_size-1) - buffer_position))
        forward_window_maximum_length = min(
                RLE_SIZE, ((buffer_size-1) - buffer_position))
        sliding_window_maximum_offset = max(0, buffer_position-WINDOW_SIZE)
        sliding_window_match_position = -1
        sliding_window_match_size = 0
        forward_window_match_value = 0
        forward_window_match_size = 0
        current_mode = None
        current_submode = None
        raw_copy_size = buffer_position - buffer_last_copy_position
        rle_bytes_left = 0

        sliding_window_match_position, sliding_window_match_size = \
                recomp_match_search3(buffer_position, file_buffer)

        # Look one step forward in the buffer, is there a matching value?
        # If yes, search further and check for a repeating value in a loop.
        # If no, continue to the rest of the function.
        matching_sequence_value = file_buffer[buffer_position]
        matching_sequence_size = 0
        while (file_buffer[buffer_position+matching_sequence_size]
                 == matching_sequence_value):
            matching_sequence_size += 1
            if matching_sequence_size >= forward_window_maximum_length:
                break

            # If we find a sequence of matching values, save them.
            if matching_sequence_size >= 1:
                forward_window_match_value = matching_sequence_value
                forward_window_match_size = matching_sequence_size

        zero_window_match_size = 0
        if OPTIMIZE_ZEROES:
            while True:
                i = buffer_position + zero_window_match_size
                if i >= len(file_buffer):
                    break
                if file_buffer[i] != 0:
                    break
                zero_window_match_size += 1
            zero_window_match_size = min(zero_window_match_size, 257)

        # Try to pick which mode works best with the current values.
        if sliding_window_match_size >= 3:
            current_mode = MODE_WINDOW_COPY
        elif forward_window_match_size >= 3:
            current_mode = MODE_RLE_WRITE_A
            if forward_window_match_value != 0:
                current_submode = MODE_RLE_WRITE_A
                if forward_window_match_size > COPY_SIZE:
                    rle_bytes_left = forward_window_match_size
            else:
                if forward_window_match_size <= COPY_SIZE:
                    current_submode = MODE_RLE_WRITE_B
                else:
                    current_submode = MODE_RLE_WRITE_C
        elif (forward_window_match_size >= 2 and
                forward_window_match_value == 0):
            current_mode = MODE_RLE_WRITE_A
            current_submode = MODE_RLE_WRITE_B

        if zero_window_match_size > max(sliding_window_match_size,
                                        forward_window_match_size):
            current_mode = MODE_RLE_WRITE_A
            current_submode = MODE_RLE_WRITE_C
            forward_window_match_size = zero_window_match_size

        # Write a raw copy command when these following conditions are met:
        # The current mode is set and there are raw bytes available to be copied.
        # The raw byte length exceeds the maximum length that can be stored.
        # Raw bytes need to be written due to the proximity to the end of the buffer.
        if ((current_mode is not None and raw_copy_size >=1) or
                raw_copy_size >= 0x1f or buffer_position+1 == buffer_size):
            if buffer_position+1 == buffer_size:
                raw_copy_size = buffer_size - buffer_last_copy_position
            write_buffer[write_position] = \
                    MODE_RAW_COPY | (raw_copy_size & 0x1f)
            write_position += 1
            for written_bytes in range(0, raw_copy_size):
                write_buffer[write_position] = \
                        file_buffer[buffer_last_copy_position]
                write_position += 1
                buffer_last_copy_position += 1

        if current_mode == MODE_WINDOW_COPY:
            value = (buffer_position - sliding_window_match_position) & 0x300
            value >>= 8
            value |= (((sliding_window_match_size-2) & 0x1f) << 2)
            value |= MODE_WINDOW_COPY
            write_buffer[write_position] = value
            write_position += 1
            write_buffer[write_position] = \
                    (buffer_position - sliding_window_match_position) & 0xff
            write_position += 1
            buffer_position += sliding_window_match_size
            buffer_last_copy_position = buffer_position

        elif current_mode == MODE_RLE_WRITE_A:
            if current_submode == MODE_RLE_WRITE_A:
                if rle_bytes_left > 0:
                    while rle_bytes_left > 0:
                        # Dump raw bytes if we have less than two bytes left,
                        # not doing so would cause an underflow error.
                        if rle_bytes_left < 2:
                            write_buffer[write_position] = \
                                    MODE_RAW_COPY | (rle_bytes_left & 0x1f)
                            write_position += 1
                            for written_bytes in range(0, rle_bytes_left):
                                write_buffer[write_position] = \
                                        forward_window_match_value & 0xff
                                write_position += 1
                            rle_bytes_left = 0
                            break

                        value = (min(rle_bytes_left, COPY_SIZE) - 2) & 0x1f
                        value |= MODE_RLE_WRITE_A
                        write_buffer[write_position] = value
                        write_position += 1
                        write_buffer[write_position] = \
                                forward_window_match_value & 0xff
                        write_position += 1
                        rle_bytes_left -= COPY_SIZE
                else:
                    value = (forward_window_match_size - 2) & 0x1f
                    write_buffer[write_position] = MODE_RLE_WRITE_A | value
                    write_position += 1
                    write_buffer[write_position] = \
                            forward_window_match_value & 0xff
                    write_position += 1
            elif current_submode == MODE_RLE_WRITE_B:
                value = (forward_window_match_size - 2) & 0x1f
                write_buffer[write_position] = MODE_RLE_WRITE_B | value
                write_position += 1
            elif current_submode == MODE_RLE_WRITE_C:
                if OPTIMIZE_ZEROES:
                    assert forward_window_match_size == zero_window_match_size
                window_end = buffer_position + forward_window_match_size
                assert set(file_buffer[buffer_position:window_end]) == {0}
                write_buffer[write_position] = MODE_RLE_WRITE_C
                write_position += 1
                write_buffer[write_position] = \
                        (forward_window_match_size - 2) & 0xff
                write_position += 1
            buffer_position += forward_window_match_size
            buffer_last_copy_position = buffer_position
        else:
            buffer_position += 1

    write_buffer[0] = 0
    write_buffer[1] = (write_position >> 16) & 0xff
    write_buffer[2] = (write_position >> 8) & 0xff
    write_buffer[3] = write_position & 0xff

    recomp = bytes(write_buffer[:write_position])
    if verify:
        verify_data = recompress_lzkn64(decomp)
        a = decompress_lzkn64(verify_data)
        b = decompress_lzkn64(recomp)
        assert a == b

    assert decompress(recomp[4:], validation_data=decomp) == decomp
    return recomp


if __name__ == '__main__':
    source_file = argv[1]
    offset = int(argv[2], 0x10)
    validation_data = None
    if len(argv) > 3:
        validation_file = argv[3]
        with open(validation_file, 'r+b') as f:
            validation_data = f.read()

    output_file = 'tmp.output.bin'

    print('TESTING DECOMPRESSION')
    with open(source_file, 'r+b') as f:
        decomp = decompress_from_file(f, offset, validation_data)
    print('TESTING RECOMPRESSION')
    recomp = recompress(decomp)
    print('FINAL LENGTH: %s' % len(recomp))

    with open(output_file, 'r+b') as f:
        f.write(decomp)
