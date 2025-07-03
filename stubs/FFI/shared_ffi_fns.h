#ifndef SHARED_FFI_FNS
#define SHARED_FFI_FNS

#include <stdio.h>

// A macro for printing debugging info
#define DEBUG_MODE 0
#if DEBUG_MODE
#define DEBUG_PRINTF(...) fprintf(stderr, __VA_ARGS__)
#else
#define DEBUG_PRINTF(...)
#endif

int qword_to_int(unsigned char *b);

void int_to_qword(int i, unsigned char *b);

long long byte8_to_longlong(unsigned char *b);

#endif
