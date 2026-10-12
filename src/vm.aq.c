#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t V;
#define TAG_MASK 0xFFFF000000000000ull
#define TAG_PTR  0xFFF9000000000000ull
#define NOTOK    TAG_PTR  // null pointer: "no reuse token"
