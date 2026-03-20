#ifndef LATTE_INTERNALS
#define LATTE_INTERNALS

#define internal(x) __lat_builtin_##x

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

typedef char* string;

void internal(printInt)(int64_t x);

void internal(printString)(string s);

int64_t internal(readInt)(void);

string internal(readString)(void);
string internal(strcat)(string s1, string s2);

void internal(makeError)(void);

void * internal(heap_alloc)(int64_t size);
#endif /* LATTE_INTERNALS */