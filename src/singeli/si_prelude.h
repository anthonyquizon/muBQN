// C definitions for the names that vendored CBQN Singeli kernels emit.
// muDefs.singeli covers the CBQN-specific names. The rest come from base,
// f64, cmp, bits, hashtab, select and fold.
// Include after vm.c's value definitions (V, H, TAG_CHR) and before any
// generated kernel file.
// Derived from CBQN's src/utils/includeSingeli.h (dzaima and contributors),
// used under MPL2.
#ifndef SI_PRELUDE_H
#define SI_PRELUDE_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Type names spelled by fmt_type{} in emitted code.
typedef int8_t i8;   typedef int16_t i16;   typedef int32_t i32;   typedef int64_t i64;
typedef uint8_t u8;  typedef uint16_t u16;  typedef uint32_t u32;  typedef uint64_t u64;
typedef double f64;

// ---- base.singeli, f64.singeli
#define si_unreachable() __builtin_unreachable()
#define ASSERT_HOM(VAL, K, W)  // TODO debug check, see CBQN's assert_hom_impl
#define si_fatal(MSG) (fprintf(stderr, "singeli: %s\n", MSG), abort())
static inline f64 interp_f64(u64 x) { f64 r; memcpy(&r, &x, 8); return r; }

// ---- boxed values (muDefs bcall). x is a V.
static inline bool si_q_f64(u64 x) { return is_num(x); }
static inline bool si_q_c32(u64 x) { return is_chr(x); }
static inline bool si_q_c8 (u64 x) { return is_chr(x) && chr(x) < 0x100; }
static inline bool si_q_c16(u64 x) { return is_chr(x) && chr(x) < 0x10000; }
static inline f64 si_o2f(u64 x) { return num(x); }
static inline i32 si_o2i(u64 x) { return (i32)num(x); }
static inline u32 si_o2c(u64 x) { return chr(x); }

// q_f<T>o: write (T)x to *out and say whether that was exact.
#define SI_QFO(T) \
  static inline bool q_f##T##o(T *out, f64 x) { return x == (f64)(*out = (T)x); }
SI_QFO(i8) SI_QFO(i16) SI_QFO(i32) SI_QFO(i64)
SI_QFO(u8) SI_QFO(u16) SI_QFO(u32) SI_QFO(u64)
#undef SI_QFO
// TODO: (T)x is UB when x is out of range or NaN. CBQN uses FLOAT_TO_INT;
// copy that before trusting these on hostile input.

// ---- tags and layout
#define SI_C32_TAG (TAG_CHR >> 48)
#define SI_DATA_OFFSET (sizeof(H) + sizeof(uint64_t))  // rank 1 only

// ---- scratch memory
#define SI_TALLOC(T, N) ((T *)malloc(sizeof(T) * (N)))
#define SI_TFREE(P) free(P)

// ---- hashtab.singeli: memset8/16/32/64
#define SI_MEMSET(W) \
  static inline void memset##W(u##W *p, u##W v, u64 l) { for (u64 i = 0; i < l; i++) p[i] = v; }
SI_MEMSET(8) SI_MEMSET(16) SI_MEMSET(32) SI_MEMSET(64)
#undef SI_MEMSET

// ---- cmp.singeli. fillBitsDec drops x. The kernel takes ownership of a boxed
// scalar on that path, so the caller must not drop x again.
static inline void fillBits(u64 *dst, u64 n, bool v) {
  memset(dst, v ? 0xff : 0, ((n + 63) / 64) * 8);
}
static inline void fillBitsDec(u64 *dst, u64 n, bool v, u64 x) {
  v_drop(x);
  fillBits(dst, n, v);
}
#define cmp_err() vm_error("Comparison: expected number or character")
static inline void bit_negatePtr(u64 *r, u64 *x, u64 n) { for (u64 i = 0; i < n; i++) r[i] = ~x[i]; }

// ---- defined later, beside the C that includes the matching kernel file:
//   blendArrScalarBits  (bits.singeli; see CBQN src/utils/bits.c)
//   get_spaced_mask(i)  (fold.singeli; = si_spaced_masks[i-1] from slash.singeli)
//   si_getRange_fns[5]  (select.singeli; [0] a bool range fn, [1..4] from
//                        search.singeli's simd_getRangeRaw)

#endif
