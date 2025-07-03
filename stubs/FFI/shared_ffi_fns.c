#include "shared_ffi_fns.h"

int qword_to_int(unsigned char *b)
{
  return ((b[0] << 24) | (b[1] << 16) | (b[2] << 8) | b[3]);
}

void int_to_qword(int i, unsigned char *b)
{
  b[0] = (i >> 24) & 0xFF;
  b[1] = (i >> 16) & 0xFF;
  b[2] = (i >> 8) & 0xFF;
  b[3] = i & 0xFF;
}

long long byte8_to_longlong(unsigned char *b)
{
  return (((long long)b[0] << 56) | ((long long)b[1] << 48) |
          ((long long)b[2] << 40) | ((long long)b[3] << 32) |
          ((long long)b[4] << 24) | ((long long)b[5] << 16) |
          ((long long)b[6] << 8) | (long long)b[7]);
}
