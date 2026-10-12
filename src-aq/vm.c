#include <math.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


typedef   int8_t i8;  typedef  uint8_t u8;  typedef  int16_t i16; 
typedef uint16_t u16; typedef  int32_t i32; typedef uint32_t u32; 
typedef  int64_t i64; typedef uint64_t u64; typedef double   f64; 
typedef float    f32; typedef size_t   ux;

                                               // .FF0 .111111111110000000000000000000000000000000000000000000000000000 infinity
                                               // .FF8 .111111111111000000000000000000000000000000000000000000000000000 qNaN
                                               // .FF. .111111111110nnn................................................ sNaN aka tagged aka not f64, if nnn≠0
                                               // 7FF. 0111111111110................................................... direct value with no need of refcounting
static const u16 C32_TAG = 0b0111111111110001; // 7FF1 0111111111110001................00000000000ccccccccccccccccccccc char
static const u16 TAG_TAG = 0b0111111111110010; // 7FF2 0111111111110010nnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn special value (see bi_N ect definitions further below)
static const u16 VAR_TAG = 0b0111111111110011; // 7FF3 0111111111110011ddddddddddddddddnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn variable reference
static const u16 EXT_TAG = 0b0111111111110100; // 7FF4 0111111111110100ddddddddddddddddnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn extended variable reference
static const u16 RAW_TAG = 0b0111111111110101; // 7FF5 0111111111110101nnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnnn raw 48 bits of data
static const u16 MD1_TAG = 0b1111111111110010; // FFF2 1111111111110010ppppppppppppppppppppppppppppppppppppppppppppp000 1-modifier
static const u16 MD2_TAG = 0b1111111111110011; // FFF3 1111111111110011ppppppppppppppppppppppppppppppppppppppppppppp000 2-modifier
static const u16 FUN_TAG = 0b1111111111110100; // FFF4 1111111111110100ppppppppppppppppppppppppppppppppppppppppppppp000 function
static const u16 NSP_TAG = 0b1111111111110101; // FFF5 1111111111110101ppppppppppppppppppppppppppppppppppppppppppppp000 namespace
static const u16 OBJ_TAG = 0b1111111111110110; // FFF6 1111111111110110ppppppppppppppppppppppppppppppppppppppppppppp000 custom/internal object
static const u16 ARR_TAG = 0b1111111111110111; // FFF7 1111111111110111ppppppppppppppppppppppppppppppppppppppppppppp000 array (everything else here is an atom)
static const u16 VAL_TAG = 0b1111111111110   ; // FFF. 1111111111110................................................... pointer to Value, needs refcounting

typedef union B { u64 u; f64 f; } B;

/* basis functions */


