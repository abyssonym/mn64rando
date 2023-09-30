from sys import argv
from textwrap import wrap
from colorama import Fore, Style
from subprocess import call
from os import listdir


if 'lzkn64' in listdir('.'):
    VERIFY = True
else:
    VERIFY = False


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


def flip_words(s):
    original_length = len(s)
    if len(s) % 2:
        assert s[-1] == 0
        #s = s[:-1]
        s += s[-1:]
        #import pdb; pdb.set_trace()
    s = b''.join([bytes([b, a]) for (a, b) in zip(s[::2], s[1::2])])
    s = s[:original_length]
    return s


def decompress_lzkn64(infile, outfile):
    cmd = ['./lzkn64', '-d', infile, outfile]
    call(cmd)


def recompress_lzkn64(infile, outfile):
    cmd = ['./lzkn64', '-c', infile, outfile]
    call(cmd)


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
    null = source_file.read(2)
    assert null == b'\x00\x00'
    length = int.from_bytes(source_file.read(2), byteorder='little') - 4
    #print(f'SOURCE DATA LENGTH: {length}')
    source_data = source_file.read(length)

    source_data = flip_words(source_data)
    if verify:
        initialize_temp()
        with open(TMP_INFILE, 'r+b') as f:
            f.write((len(source_data)+4).to_bytes(4))
            f.write(source_data)
        decompress_lzkn64(TMP_INFILE, TMP_OUTFILE)
        with open(TMP_OUTFILE, 'r+b') as f:
            verify_data = f.read()
        decomp = decompress(source_data, verify_data)
        assert decomp == verify_data
    else:
        decomp = decompress(source_data, validation_data)
    return decomp


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
    buffer_size = len(decomp)
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

        # Go backwards in the buffer, is there a matching value?
        # If yes, search forward and check for more matching values in a loop.
        # If no, go further back and repeat.
        for search_position in range(
                buffer_position-1, sliding_window_maximum_offset, -1):
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
        initialize_temp()
        with open(TMP_INFILE, 'r+b') as f:
            f.write(decomp)
        recompress_lzkn64(TMP_INFILE, TMP_OUTFILE)
        with open(TMP_TESTFILE, 'r+b') as f:
            f.write(recomp)
        with open(TMP_OUTFILE, 'r+b') as f:
            verify_data = f.read()
        for i in range(4, len(verify_data)):
            if verify_data[4:i] == recomp[4:i]:
                pass
            else:
                break
        assert verify_data == recomp

    assert decompress(recomp[4:], validation_data=decomp) == decomp


if __name__ == '__main__':
    source_file = argv[1]
    offset = int(argv[2], 0x10)
    validation_file = argv[3]
    output_file = 'tmp.output.bin'

    with open(validation_file, 'r+b') as f:
        validation_data = f.read()

    print('TESTING DECOMPRESSION')
    with open(source_file, 'r+b') as f:
        decomp = decompress_from_file(f, offset, validation_data)
    print('TESTING RECOMPRESSION')
    recomp = recompress(decomp)

    with open(output_file, 'r+b') as f:
        f.write(decomp)
