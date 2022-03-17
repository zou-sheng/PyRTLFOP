import random
from .utils import *

########################################################################
# arith 8/8, 16/8, 32/8
########################################################################
def wrapping_add(a, b, size):
    # a=self, b = n
    min = -1*(1<<(size-1))
    max = (1<<(size-1)) - 1
    offset = a > (max - b)
    a = min + (b - (max - a) - 1) if offset else a + b
    return a

ARITH_MAX = 35
def arith_8_max(length):
    return 2 * length * ARITH_MAX

def arith_8(ii, seed):
    byte = ii // ARITH_MAX // 2
    rest = ii - (byte * ARITH_MAX * 2)
    b = rest // 2
    a = seed[byte]
    add_not_sub = (rest & 1) == 0
    seed[byte] = uint8(wrapping_add(a, b, bytelen)) if add_not_sub else uint8(wrapping_add(a, -1*b, bytelen))
    return seed

def read_u16(endian, seed, byte):
    if endian == 0: #big endian
        return uint16(seed[byte+0]) << 8 | uint16(seed[byte + 1])
    else: #little endian
        return uint16(seed[byte + 1]) << 8 | uint16(seed[byte + 0])

def write_u16(endian, seed, byte, value):
    high = uint8(value >> 8)
    low = uint8(value & 0xff)
    if endian == 0: #big endian
        seed[byte+0] = high
        seed[byte+1] = low
    else: # little endian
        seed[byte + 1] = high
        seed[byte + 0] = low
    return seed

def arith_16_max(length):
    return 4 * (length-1) * ARITH_MAX

def arith_16(ii, seed):
    if not(ii is None):
        byte = ii // ARITH_MAX // 4
        rest = ii - (uint32(byte) * ARITH_MAX * 4)
        b = (rest // 4)
        add_no_sub = (rest & 2) == 0
        #0 for big endian, 1 for little endian
        endian = 0 if (rest & 1) == 1 else 1
        a = read_u16(endian, seed, byte)
        res = uint16(wrapping_add(a,b,16)) if add_no_sub else uint16(wrapping_add(a, -1*b,16))
        return write_u16(endian, seed, byte, res)
    else:
        return seed

def read_u32(endian, seed, byte):
    if endian == 0: #big endian
        return uint32(seed[byte+0]) << 24 | uint32(seed[byte + 1]) << 16 | \
               uint32(seed[byte + 2]) << 8 | uint32(seed[byte + 3])
    else: #little endian
        return uint32(seed[byte+3]) << 24 | uint32(seed[byte + 2]) << 16 | \
               uint32(seed[byte + 1]) << 8 | uint32(seed[byte + 0])

def write_u32(endian, seed, byte, value):
    byte_3 = uint8((value >> 24) & 0xff)
    byte_2 = uint8((value >> 16) & 0xff)
    byte_1 = uint8((value >> 8) & 0xff)
    byte_0 = uint8((value >> 0) & 0xff)
    if endian == 0: #big endian
        seed[byte+0] = byte_3
        seed[byte+1] = byte_2
        seed[byte+2] = byte_1
        seed[byte+3] = byte_0
    else: # little endian
        seed[byte + 3] = byte_3
        seed[byte + 2] = byte_2
        seed[byte + 1] = byte_1
        seed[byte + 0] = byte_0
    return seed

def arith_32_max(length):
    return 4 * (length-3) * ARITH_MAX

def arith_32(ii, seed):
    if not(ii is None):
        byte = ii // ARITH_MAX // 4
        rest = ii - (uint32(byte) * ARITH_MAX * 4)
        b = (rest // 4)
        add_no_sub = (rest & 2) == 0
        #0 for big endian, 1 for little endian
        endian = 0 if (rest & 1) == 1 else 1
        a = read_u32(endian, seed, byte)
        res = uint32(wrapping_add(a, b, 32)) if add_no_sub else uint32(wrapping_add(a, -1*b, 32))
        return write_u32(endian, seed, byte, res)
    else:
        return seed

########################################################################
# flip bit(s)
########################################################################
def flipbit_1_max(length):
    return length * bytelen

def flipbit_1(ii, seed):
    byte = ii // bytelen
    bit = ii - (byte * bytelen)
    seed[byte] ^= (1 << bit)
    return seed

def flipbit_2_max(length):
    return length * bytelen - 1

def flipbit_2(ii, seed):
    byte = ii // bytelen
    bit = ii - (byte * bytelen)
    seed[byte] ^= (1 << (bit + bytelen))
    seed[byte] ^= (1 << (bit + 1))
    return seed

def flipbit_4_max(length):
    return length * bytelen - 3

def flipbit_4(ii, seed):
    byte = ii // bytelen
    bit = ii - (byte * bytelen)
    seed[byte] ^= 1 << (bit + 0)
    seed[byte] ^= 1 << (bit + 1)
    seed[byte] ^= 1 << (bit + 2)
    seed[byte] ^= 1 << (bit + 3)
    return seed

########################################################################
# flip byte(s)
########################################################################
def flipbyte_1_max(length):
    return length

def flipbyte_1(ii, seed):
    seed[ii] ^= 0xFF
    return seed

def flipbyte_2_max(length):
    return length - 1

def flipbyte_2(ii, seed):
    if not(ii is None):
        seed[ii] ^= 0xff
        seed[ii + 1] ^= 0xff
    else:
        for ii in range(len(seed)):
            seed[ii] ^= 0xff
    return seed

def flipbyte_4_max(length):
    return length - 3

def flipbyte_4(ii, seed):
    if not(ii is None):
        seed[ii] ^= 0xff
        seed[ii + 1] ^= 0xff
        seed[ii + 2] ^= 0xff
        seed[ii + 3] ^= 0xff
    else:
        for ii in range(len(seed)):
            seed[ii] ^= 0xff
    return seed

########################################################################
# Interesting mutation
########################################################################
INTERESTING_8 = [-128, -1, 0, 1, 16, 32, 64, 100, 127]
def int_8_max(length):
    return length * len(INTERESTING_8)

def int_8(ii, seed):
    pos = ii // len(INTERESTING_8)
    interesting = uint8(INTERESTING_8[ii - pos*len(INTERESTING_8)])
    seed[pos] = interesting
    return seed

INTERESTING_16 = [-32768, -129, 128, 255, 256, 512, 1000, 1024, 4096, 32767]
def int_16_max(length):
    return 2 * (length-1) * len(INTERESTING_16)

def int_16(ii, seed):
    if not(ii is None):
        pos = ii // len(INTERESTING_16) // 2
        rest = ii - (pos * len(INTERESTING_16) * 2)
        interesting = uint16(INTERESTING_16[rest // 2])
        # 0 for big endian, 1 for little endian
        endian = 0 if (rest & 1) == 1 else 1
        return write_u16(endian, seed, pos, interesting)
    else:
        return seed

INTERESTING_32 = [-2147483648, -100663046, -32769, 32768, 65535, 65536, 100663045, 2147483647]
def int_32_max(length):
    return 2 * (length - 3) * len(INTERESTING_32)

def int_32(ii, seed):
    if not(ii is None):
        pos = ii // len(INTERESTING_32) // 2
        rest = ii - (pos * len(INTERESTING_32) * 2)
        interesting = uint32(INTERESTING_32[rest // 2])
        # 0 for big endian, 1 for little endian
        endian = 0 if (rest & 1) == 1 else 1
        return write_u32(endian, seed, pos, interesting)
    else:
        return seed

########################################################################
# other non-deterministic mutators
########################################################################
def random8_max(length):
    return length

def random8(pos, seed):
    flips = uint8(random.choice(range(255))+1)
    seed[pos] ^= flips
    return seed

########################################################################
# prepare and finalize seed mutate
########################################################################

def split_seed(seed):
    # split seed in every 8-bit form and translate it into u8
    # if the length of the last one is less than 8, padding zero to it
    length = bytelen
    seed_bytes = []
    for i in range(len(seed)//length):
        seed_bytes.append(uint8(int(seed[i*length:(i+1)*length], 2)))
    #print(seed_bytes)

    if len(seed)/length - len(seed)//length > 0:
        #print(seed, uint8(int(seed[(len(seed)//length)*length:], 2)))
        last = bytelen - (len(seed) - (len(seed) // length) * length)
        seed_bytes.append(uint8(int(seed[(len(seed)//length)*length:] + '0'*last, 2)))
    else:
        last = 0

    #print(seed_bytes, last)
    return seed_bytes, last

def concate_seed(seed, last):
    binseed = list(map(lambda x: int2bin(x, bytelen), seed))
    conseed = ''.join(binseed)
    if last == 0:
        return conseed
    else:
        return conseed[:0-last]

def deterministic_mutate(seed, mutator):
    byte_seed, last = split_seed(seed)
    mutations = []
    for ii in range(mutator[1](len(byte_seed))):
        byte_seed = mutator[0](ii, byte_seed)
        mutations.append(concate_seed(byte_seed, last))
    return mutations

def non_deterministic_mutate(seed, mutator):
    byte_seed, last = split_seed(seed)
    try:
        ii = random.choice(range(mutator[1](len(byte_seed))))
    except:
        ii = None
    byte_seed = mutator[0](ii, byte_seed)
    return [concate_seed(byte_seed, last)]

deterministic_mutators = {
    "bitflip  1/1": (flipbit_1, flipbit_1_max),
    "bitflip  2/1": (flipbit_2, flipbit_2_max),
    "bitflip  4/1": (flipbit_4, flipbit_4_max),
    "bitflip  8/8": (flipbyte_1, flipbyte_1_max),
    "bitflip 16/8": (flipbyte_2, flipbyte_2_max),
    "bitflip 32/8": (flipbyte_4, flipbyte_4_max),
    "arith    8/8": (arith_8, arith_8_max),
    "arith   16/8": (arith_16, arith_16_max),
    "arith   32/8": (arith_32, arith_32_max),
    "interest 8/8": (int_8, int_8_max),
    "interest 16/8": (int_16, int_16_max),
    "interest 32/8": (int_32, int_32_max)
}

non_deterministic_mutators = {
    "bitflip  1/1": (flipbit_1, flipbit_1_max),
    #"bitflip  2/1": (flipbit_2, flipbit_2_max),
    #"bitflip  4/1": (flipbit_4, flipbit_4_max),
    #"bitflip  8/8": (flipbyte_1, flipbyte_1_max),
    #"bitflip 16/8": (flipbyte_2, flipbyte_2_max),
    #"bitflip 32/8": (flipbyte_4, flipbyte_4_max),
    "arith    8/8": (arith_8, arith_8_max),
    "arith   16/8": (arith_16, arith_16_max),
    "arith   32/8": (arith_32, arith_32_max),
    "interest 8/8": (int_8, int_8_max),
    "interest 16/8": (int_16, int_16_max),
    "interest 32/8": (int_32, int_32_max),
    "random 8": (random8, random8_max)
}
