########################################################################
# utils
########################################################################

bytelen = 8

def uint(v, ring = 0xFFFFFFFF):
    return (v if isinstance(v, int) else int(v)) & ring

def uint8(v):
    return uint(v, 0xFF)

def uint16(v):
    return uint(v, 0xFFFF)

def uint32(v):
    return uint(v, 0xFFFFFFFF)

def int2bin(n, count=24):
    """returns the binary of integer n, using count number of digits"""
    return "".join([str((n >> y) & 1) for y in range(count-1, -1, -1)])