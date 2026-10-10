// vm.c: muBQN. All hand-written C lives in this one file (see docs/design.md).
//
// Sections, in order:
//   runtime      values, rc, reuse tokens
//   kernels      plain (dst, src, n) loops; scalar fallbacks until Singeli
//   basis        kernels as value-level operations with an ownership convention.
//                C generated from the primitive dialect calls these.
//   generated    #include "gen/*.c" goes here (none yet)
//   interpreter  milestone 1
//   main         -DPRIM_TEST builds the test harness instead
//
// Build: cc -std=c11 -Wall -O2 src/vm.c -o vm
// Test:  cc -std=c11 -Wall -O2 -DPRIM_TEST src/vm.c -o vm-test && ./vm-test

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Runtime and basis functions exist for generated code, which may not call
// all of them yet.
#pragma GCC diagnostic ignored "-Wunused-function"

static void die(const char *msg) { fprintf(stderr, "vm: %s\n", msg); exit(1); }

// ===================================================================== runtime

// ---- values: NaN-boxed. Numbers are plain doubles (NaNs canonicalised);
// heap pointers live in a negative quiet-NaN space above every real double.
typedef uint64_t V;
#define TAG_MASK 0xFFFF000000000000ull
#define TAG_PTR  0xFFF9000000000000ull
#define NOTOK    TAG_PTR  // null pointer: "no reuse token"

static inline int is_num(V v) { return v < TAG_PTR; }
static inline int is_ptr(V v) { return (v & TAG_MASK) == TAG_PTR; }
static inline double num(V v) { double d; memcpy(&d, &v, 8); return d; }
static inline V mk_num(double d) {
  if (d != d) return 0x7FF8000000000000ull;
  V v; memcpy(&v, &d, 8); return v;
}

// ---- heap objects: header, then shape[rank], then len 8-byte elements.
// T_F64 elements are doubles, T_VAL elements are V; both are 8 bytes, and a
// number's V bits are its double bits, so copying code treats them alike.
enum { T_F64, T_VAL, T_TOK };
enum { F_STATIC = 1 };  // static slots and constants: never reference counted

typedef struct H {
  int32_t rc;
  uint8_t type, rank, flags, _pad;
  uint64_t len;  // element count
  uint64_t cap;  // block size in bytes, for reuse
} H;

static inline H *ptr(V v) { return (H *)(uintptr_t)(v & ~TAG_MASK); }
static inline V mk_ptr(H *h) { return (V)(uintptr_t)h | TAG_PTR; }
static inline uint64_t *shp(H *h) { return (uint64_t *)(h + 1); }
static inline V *vals(H *h) { return (V *)(shp(h) + h->rank); }
static inline double *f64s(H *h) { return (double *)(shp(h) + h->rank); }
static inline int unique(H *h) { return h->rc == 1 && !(h->flags & F_STATIC); }

static long live_objs;  // must be 0 at exit
static long reused;     // stats: blocks recycled through reuse tokens

static void h_free(H *h);

static inline void v_dup(V v) {
  if (!is_ptr(v) || v == NOTOK) return;
  H *h = ptr(v);
  if (!(h->flags & F_STATIC)) h->rc++;
}
static inline void v_drop(V v) {
  if (!is_ptr(v) || v == NOTOK) return;
  H *h = ptr(v);
  if (!(h->flags & F_STATIC) && --h->rc == 0) h_free(h);
}

static void h_drop_children(H *h) {
  if (h->type == T_VAL)
    for (uint64_t i = 0; i < h->len; i++) v_drop(vals(h)[i]);
}
static void h_free(H *h) { h_drop_children(h); live_objs--; free(h); }

static H *h_alloc(uint8_t type, uint8_t rank, uint64_t len) {
  size_t bytes = sizeof(H) + (rank + len) * 8;
  H *h = malloc(bytes);
  if (!h) die("out of memory");
  *h = (H){.rc = 1, .type = type, .rank = rank, .len = len, .cap = bytes};
  live_objs++;
  return h;
}
static H *h_list(uint8_t type, uint64_t n) {
  H *h = h_alloc(type, 1, n);
  shp(h)[0] = n;
  return h;
}
static H *h_like(H *a) {  // fresh array with a's type and shape
  H *r = h_alloc(a->type, a->rank, a->len);
  memcpy(shp(r), shp(a), a->rank * 8);
  return r;
}

// ---- reuse tokens. drop_reuse consumes v; if it held the only reference,
// its children are dropped and its block becomes a token for alloc_at.
static V drop_reuse(V v) {
  if (!is_ptr(v)) return NOTOK;
  H *h = ptr(v);
  if (h->flags & F_STATIC) return NOTOK;
  if (h->rc != 1) { h->rc--; return NOTOK; }
  h_drop_children(h);
  h->type = T_TOK;  // a token dropped unused is just freed
  return v;
}
static H *alloc_at(V tok, uint8_t type, uint8_t rank, uint64_t len) {
  size_t bytes = sizeof(H) + (rank + len) * 8;
  if (tok != NOTOK) {
    H *h = ptr(tok);
    if (h->cap >= bytes) {
      uint64_t cap = h->cap;
      *h = (H){.rc = 1, .type = type, .rank = rank, .len = len, .cap = cap};
      reused++;
      return h;
    }
    live_objs--; free(h);
  }
  return h_alloc(type, rank, len);
}

// ===================================================================== kernels
// Kernels know nothing about BQN values. Each must be correct when dst aliases
// an input, so the basis can write into a unique argument's buffer.

#define K_ARITH(name, OP)                                                     \
  static void k_##name##_vv(double *d, const double *a, const double *b,     \
                            uint64_t n) {                                     \
    for (uint64_t i = 0; i < n; i++) d[i] = a[i] OP b[i];                     \
  }                                                                           \
  static void k_##name##_vs(double *d, const double *a, double b,            \
                            uint64_t n) {                                     \
    for (uint64_t i = 0; i < n; i++) d[i] = a[i] OP b;                        \
  }                                                                           \
  static void k_##name##_sv(double *d, double a, const double *b,            \
                            uint64_t n) {                                     \
    for (uint64_t i = 0; i < n; i++) d[i] = a OP b[i];                        \
  }
K_ARITH(add, +)
K_ARITH(sub, -)
K_ARITH(mul, *)
#undef K_ARITH

static void k_range(double *d, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) d[i] = (double)i;
}

// d[i] = s[idx[i]], negative indices counting from the end. Indices must
// already be checked. Copies 8-byte elements, so it serves T_F64 and T_VAL.
static void k_gather(uint64_t *d, const double *idx, const uint64_t *s,
                     uint64_t len, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) {
    double j = idx[i];
    d[i] = s[(uint64_t)(j < 0 ? j + (double)len : j)];
  }
}

// ======================================================================= basis
// Lists only (rank ≤ 1 arguments) unless a comment says otherwise. Each
// function states, per argument, whether it consumes or borrows.

static H *as_f64(V v, const char *nm) {
  if (!is_ptr(v) || ptr(v)->type != T_F64) {
    fprintf(stderr, "vm: %s: ", nm);
    die("expected numbers");
  }
  return ptr(v);
}
static int same_shape(H *a, H *b) {
  return a->rank == b->rank && !memcmp(shp(a), shp(b), a->rank * 8);
}

// ≠𝕩: borrows x
static V b_len(V x) {
  return mk_num(is_ptr(x) && ptr(x)->rank ? (double)shp(ptr(x))[0] : 1);
}

// ↕𝕩: consumes x (a number)
static V b_range(V x) {
  double n = num(x);
  if (!is_num(x) || n < 0 || n != floor(n) || n > 9007199254740992.0)
    die("↕: 𝕩 must be a natural number");
  H *r = h_list(T_F64, (uint64_t)n);
  k_range(f64s(r), r->len);
  return mk_ptr(r);
}

// 𝕨+𝕩, 𝕨-𝕩, 𝕨×𝕩: consume w and x. The result goes into a unique argument's
// buffer when there is one.
typedef void Kvv(double *, const double *, const double *, uint64_t);
typedef void Kvs(double *, const double *, double, uint64_t);
typedef void Ksv(double *, double, const double *, uint64_t);

static inline V arith(V w, V x, const char *nm, Kvv *vv, Kvs *vs, Ksv *sv) {
  if (is_num(w) && is_num(x)) {
    double a = num(w), b = num(x);
    double d; vv(&d, &a, &b, 1);
    return mk_num(d);
  }
  if (is_num(w) || is_num(x)) {
    V arr = is_num(w) ? x : w;
    H *a = as_f64(arr, nm);
    H *r = unique(a) ? a : h_like(a);
    if (is_num(w)) sv(f64s(r), num(w), f64s(a), a->len);
    else           vs(f64s(r), f64s(a), num(x), a->len);
    if (r != a) v_drop(arr);
    return mk_ptr(r);
  }
  H *a = as_f64(w, nm), *b = as_f64(x, nm);
  if (!same_shape(a, b)) {
    fprintf(stderr, "vm: %s: ", nm);
    die("shape mismatch");
  }
  H *r = unique(a) ? a : unique(b) ? b : h_like(a);
  vv(f64s(r), f64s(a), f64s(b), a->len);
  if (r != a) v_drop(w);
  if (r != b) v_drop(x);
  return mk_ptr(r);
}
static V b_add(V w, V x) { return arith(w, x, "+", k_add_vv, k_add_vs, k_add_sv); }
static V b_sub(V w, V x) { return arith(w, x, "-", k_sub_vv, k_sub_vs, k_sub_sv); }
static V b_mul(V w, V x) { return arith(w, x, "×", k_mul_vv, k_mul_vs, k_mul_sv); }

// 𝕨⊏𝕩: consumes w, borrows x. 𝕩 must be a list; 𝕨 may have any shape and
// gives the result its shape. Writes into w's block when w is unique.
static V b_select(V w, V x) {
  if (!is_ptr(x) || ptr(x)->rank != 1) die("⊏: 𝕩 must be a list");
  H *s = ptr(x);
  uint64_t len = s->len;
  int atom = is_num(w);
  double wn = atom ? num(w) : 0;
  H *a = atom ? NULL : as_f64(w, "⊏");
  const double *idx = atom ? &wn : f64s(a);
  uint64_t n = atom ? 1 : a->len;
  for (uint64_t i = 0; i < n; i++) {
    double j = idx[i];
    if (j != floor(j) || j < -(double)len || j >= (double)len)
      die("⊏: index out of bounds");
  }
  H *r;
  if (atom) r = h_alloc(s->type, 0, 1);
  else if (unique(a)) { r = a; r->type = s->type; }
  else r = h_like(a), r->type = s->type;
  k_gather((uint64_t *)vals(r), idx, (const uint64_t *)vals(s), len, n);
  if (r->type == T_VAL)
    for (uint64_t i = 0; i < n; i++) v_dup(vals(r)[i]);
  if (!atom && r != a) v_drop(w);
  return mk_ptr(r);
}

// ================================================================== generated
// #include "gen/kernels.c"   Singeli output (later)
// #include "gen/prims.c"     primitive dialect output (step 2)

// ================================================================ interpreter
// Milestone 1.

// ======================================================================== main

#ifdef PRIM_TEST

// ---- show: compact BQN-like text. Matches CBQN's •Show for numbers and
// lists; rank 0 prints as <x instead of CBQN's boxed layout.
typedef struct { char *p; size_t n, cap; } Buf;
static void put(Buf *b, const char *s) {
  size_t k = strlen(s);
  if (b->n + k + 1 > b->cap) {
    b->cap = 2 * (b->n + k + 1);
    b->p = realloc(b->p, b->cap);
    if (!b->p) die("out of memory");
  }
  memcpy(b->p + b->n, s, k + 1);
  b->n += k;
}
static void show_num(Buf *b, double d) {
  char s[40], t[48];
  if (d != d) { put(b, "NaN"); return; }
  if (isinf(d)) { put(b, d < 0 ? "¯∞" : "∞"); return; }
  if (d == floor(d) && fabs(d) < 9007199254740992.0) {
    snprintf(s, sizeof s, "%.0f", d == 0 ? 0 : d);
  } else {
    for (int p = 1; p <= 17; p++) {  // shortest text that reads back exactly
      snprintf(s, sizeof s, "%.*g", p, d);
      if (strtod(s, NULL) == d) break;
    }
  }
  size_t j = 0;  // '-' → '¯', and "e+05"/"e-05" → "e5"/"e¯5"
  for (char *c = s; *c; c++) {
    if (*c == '-') { memcpy(t + j, "¯", 2); j += 2; }
    else if (*c == '+') {}
    else if (*c == '0' && c > s && (c[-1] == 'e' || c[-1] == '+' || c[-1] == '-') &&
             strchr(s, 'e') && strchr(s, 'e') < c) {}
    else t[j++] = *c;
  }
  t[j] = 0;
  put(b, t);
}
static void show_v(Buf *b, V v) {
  if (is_num(v)) { show_num(b, num(v)); return; }
  H *h = ptr(v);
  if (h->rank == 0) { put(b, "<"); show_v(b, vals(h)[0]); return; }
  if (h->rank > 1) { put(b, "(rank>1)"); return; }
  if (h->len == 0) { put(b, "⟨⟩"); return; }
  put(b, "⟨");
  for (uint64_t i = 0; i < h->len; i++) { put(b, " "); show_v(b, vals(h)[i]); }
  put(b, " ⟩");
}

static int fails;
// Consumes v.
static void check(const char *name, V v, const char *want) {
  Buf b = {0};
  show_v(&b, v);
  v_drop(v);
  if (strcmp(b.p, want)) {
    printf("FAIL %s: got %s, want %s\n", name, b.p, want);
    fails++;
  }
  free(b.p);
}
static V list(const double *xs, uint64_t n) {
  H *h = h_list(T_F64, n);
  memcpy(f64s(h), xs, n * 8);
  return mk_ptr(h);
}
#define LIST(...) \
  list((const double[]){__VA_ARGS__}, sizeof((double[]){__VA_ARGS__}) / 8)

// Hand-written stand-in for what gen/prims.c will contain, after Perceus:
//   Reverse ← {n←≠𝕩 ⋄ (n-1+↕n)⊏𝕩}
// n is a number, so its dup/drop are specialised away.
static V prim_reverse(V x) {  // consumes x
  V n = b_len(x);
  V t = b_range(n);
  t = b_add(mk_num(1), t);
  t = b_sub(n, t);
  V r = b_select(t, x);
  v_drop(x);
  return r;
}

int main(void) {
  // Expected strings come from CBQN's •Show.
  check("range", b_range(mk_num(5)), "⟨ 0 1 2 3 4 ⟩");
  check("range 0", b_range(mk_num(0)), "⟨⟩");
  check("add", b_add(LIST(1, 2, 3), LIST(10, 20, 30)), "⟨ 11 22 33 ⟩");
  check("sub sv", b_sub(mk_num(10), LIST(1, 2, 3)), "⟨ 9 8 7 ⟩");
  check("sub vs", b_sub(LIST(1, 2, 3), mk_num(10)), "⟨ ¯9 ¯8 ¯7 ⟩");
  check("mul atoms", b_mul(mk_num(6), mk_num(7)), "42");
  check("nums", LIST(0.1, -2.5, 1e20, 1.0 / 3, INFINITY, -INFINITY, 1e-7),
        "⟨ 0.1 ¯2.5 1e20 0.3333333333333333 ∞ ¯∞ 1e¯7 ⟩");
  V x = LIST(10, 11, 12, 13, 14);  // ⊏ borrows 𝕩
  check("select", b_select(LIST(4, -1, 0), x), "⟨ 14 14 10 ⟩");
  check("select atom", b_select(mk_num(2), x), "<12");
  v_drop(x);
  check("reverse", prim_reverse(LIST(10, 11, 12, 13, 14)),
        "⟨ 14 13 12 11 10 ⟩");
  check("reverse empty", prim_reverse(LIST()), "⟨⟩");

  // Reuse: a unique argument's buffer becomes the result.
  V a = LIST(1, 2, 3);
  V r = b_add(a, mk_num(1));
  if (r != a) { printf("FAIL add did not reuse its unique argument\n"); fails++; }
  check("add in place", r, "⟨ 2 3 4 ⟩");

  // A shared argument is left alone.
  V s = LIST(1, 2, 3);
  v_dup(s);
  check("reverse shared", prim_reverse(s), "⟨ 3 2 1 ⟩");
  check("shared intact", s, "⟨ 1 2 3 ⟩");

  if (live_objs != 0) {
    printf("FAIL rc balance: %ld objects live at exit\n", live_objs);
    fails++;
  }
  printf("%s (%d failures)\n", fails ? "FAILED" : "ok", fails);
  return fails != 0;
}

#else

int main(void) {
  fputs("vm: interpreter not written yet (milestone 1); "
        "build with -DPRIM_TEST for the primitive tests\n", stderr);
  return 1;
}

#endif
