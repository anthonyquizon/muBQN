// vm.c: register VM for memBQN (sketch, see docs/design.md)
//
// Two halves:
//   runtime     values, rc, reuse tokens, primitives. Moves to rt.c/rt.h once
//               a C backend exists, since generated C links the same code.
//   interpreter register instructions, frames, and the ownership checker.
//
// Build: cc -std=c11 -Wall -O2 src/vm.c -o vm      (-DVM_CHECK=0 to disable checks)

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef VM_CHECK
#define VM_CHECK 1
#endif

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
// number's V bits are its double bits, so most code treats them alike.
enum { T_F64, T_VAL, T_FN, T_TOK };
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
  // T_FN: drop captured values here once flat closures exist (milestone 2)
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

// ---- functions. A function value is a heap object pointing at code.
// Top-level functions are static objects; flat closures add captures later.
typedef struct { uint8_t op; uint16_t d, a, b, c; } Ins;
typedef struct Fn {
  const char *name;
  const Ins *code;
  const V *consts;
  uint16_t nregs, nparams;
  uint32_t borrowed;  // bit i: parameter i is borrowed (set by borrow inference)
} Fn;
typedef struct { H h; const Fn *fn; } FnObj;

static const Fn *fn_of(V v) {
  if (!is_ptr(v) || ptr(v)->type != T_FN) die("not a function");
  return ((FnObj *)ptr(v))->fn;
}

static V vm_call(const Fn *f, V *args);

// ---- primitives. Each has a fixed ownership convention per argument.

// ⟨…⟩: consumes tok and the elements
static V p_list(V tok, V *xs, uint16_t n) {
  int allnum = 1;
  for (uint16_t i = 0; i < n; i++) allnum &= is_num(xs[i]);
  H *h = alloc_at(tok, allnum ? T_F64 : T_VAL, 1, n);
  shp(h)[0] = n;
  memcpy(vals(h), xs, n * 8u);
  return mk_ptr(h);
}

// ≠𝕩: borrows x
static V p_len(V x) {
  return mk_num(is_ptr(x) && ptr(x)->rank ? (double)shp(ptr(x))[0] : 1);
}

static H *as_f64(V v) {
  if (ptr(v)->type != T_F64) die("+: only flat number arrays in this sketch");
  return ptr(v);
}
static int same_shape(H *a, H *b) {
  return a->rank == b->rank && !memcmp(shp(a), shp(b), a->rank * 8);
}

// 𝕨+𝕩: consumes w and x; writes into whichever array argument is unique
static V p_add(V w, V x) {
  if (is_num(w) && is_num(x)) return mk_num(num(w) + num(x));
  if (is_num(w)) { V t = w; w = x; x = t; }  // + commutes; - and ÷ can't do this
  H *a = as_f64(w);
  double *ad = f64s(a);
  if (is_num(x)) {
    double s = num(x);
    H *r = unique(a) ? a : h_like(a);
    double *rd = f64s(r);
    for (uint64_t i = 0; i < a->len; i++) rd[i] = ad[i] + s;
    if (r != a) v_drop(w);
    return mk_ptr(r);
  }
  H *b = as_f64(x);
  if (!same_shape(a, b)) die("+: shape mismatch");
  double *bd = f64s(b);
  H *r = unique(a) ? a : unique(b) ? b : h_like(a);
  double *rd = f64s(r);
  for (uint64_t i = 0; i < a->len; i++) rd[i] = ad[i] + bd[i];
  if (r != a) v_drop(w);
  if (r != b) v_drop(x);
  return mk_ptr(r);
}

// ⌽𝕩: consumes x; reverses in place when unique
static V p_rev(V x) {
  if (!is_ptr(x) || ptr(x)->rank == 0) die("⌽: needs rank ≥ 1");
  H *a = ptr(x);
  uint64_t n = shp(a)[0], c = n ? a->len / n : 0;  // cell count, cell size
  V *s = vals(a);
  if (unique(a)) {
    if (n > 1)
      for (uint64_t i = 0, j = n - 1; i < j; i++, j--)
        for (uint64_t k = 0; k < c; k++) {
          V t = s[i*c + k]; s[i*c + k] = s[j*c + k]; s[j*c + k] = t;
        }
    return x;
  }
  H *r = h_like(a);
  V *d = vals(r);
  for (uint64_t i = 0; i < n; i++) memcpy(d + i*c, s + (n-1-i)*c, c * 8);
  if (a->type == T_VAL)
    for (uint64_t i = 0; i < a->len; i++) v_dup(d[i]);
  v_drop(x);
  return mk_ptr(r);
}

// 𝔽¨𝕩: borrows f, consumes x; results go into x's cells when x is unique
static V p_each(V f, V x) {
  const Fn *g = fn_of(f);
  if (g->nparams != 1) die("¨: monadic only in this sketch");
  if (!is_ptr(x)) die("¨: atom 𝕩 not in this sketch");
  H *a = ptr(x);
  H *r = unique(a) ? a : h_like(a);
  V *s = vals(a), *d = vals(r);
  int brw = g->borrowed & 1;
  for (uint64_t i = 0; i < a->len; i++) {
    V e = s[i];
    if (!brw && r != a) v_dup(e);  // callee takes a ref; a keeps its own
    V y = vm_call(g, &e);
    if (brw && r == a) v_drop(e);  // we owned the cell's ref; callee only borrowed
    if (r->type == T_F64 && !is_num(y))
      die("¨: non-number result into number array (TODO: widen to T_VAL)");
    d[i] = y;
  }
  if (r != a) v_drop(x);
  return mk_ptr(r);
}

// ================================================================= interpreter

// Operand fields: d = destination register, a/b/c = sources.
enum {
  OP_CONST,       // d = consts[a]
  OP_DUP,         // dup a
  OP_DROP,        // drop a
  OP_DROP_REUSE,  // d = drop_reuse a          (d is a token)
  OP_LIST,        // d = ⟨b … b+c-1⟩ at token a (a = NOREG: fresh allocation)
  OP_ADD,         // d = a + b
  OP_REV,         // d = ⌽ a
  OP_LEN,         // d = ≠ a
  OP_EACH,        // d = a¨ b
  OP_CALL,        // d = a(b … b+c-1)
  OP_RET,         // return a
};
#define NOREG 0xFFFF

// Ownership checker. Shadows each register with the number of owned refs it
// holds, plus a flag for borrowed parameters. Every instruction declares how
// it uses each operand, so a Perceus bug stops at the exact instruction.
#if VM_CHECK
static void chk_fail(const Fn *f, size_t pc, unsigned r, const char *what) {
  fprintf(stderr, "vm: ownership error in %s at pc %zu: r%u %s\n",
          f->name, pc, r, what);
  exit(1);
}
#define BORROW(r) do {                                           \
    if (!(own[r] > 0 || brw[r])) chk_fail(f, pc, r, "read while dead"); \
  } while (0)
#define TAKE(r) do {                                             \
    if (own[r] <= 0) chk_fail(f, pc, r, "consumed without an owned ref"); \
    own[r]--;                                                    \
  } while (0)
#define DEF(r) do {                                              \
    if (own[r] > 0) chk_fail(f, pc, r, "overwritten while owning a ref (leak)"); \
    own[r] = 1;                                                  \
    brw[r] = 0;                                                  \
  } while (0)
#define DUPR(r) do { BORROW(r); own[r]++; } while (0)
#else
#define BORROW(r) ((void)0)
#define TAKE(r) ((void)0)
#define DEF(r) ((void)0)
#define DUPR(r) ((void)0)
#endif

// Callee owns its arguments except borrowed ones. Frames are C stack VLAs;
// recursion through vm_call is also how ¨ ⌜ ´ call back into compiled code.
static V vm_call(const Fn *f, V *args) {
  V r[f->nregs];
#if VM_CHECK
  int16_t own[f->nregs];
  uint8_t brw[f->nregs];
  memset(own, 0, sizeof own);
  memset(brw, 0, sizeof brw);
#endif
  for (uint16_t i = 0; i < f->nparams; i++) {
    r[i] = args[i];
#if VM_CHECK
    if (f->borrowed >> i & 1) brw[i] = 1; else own[i] = 1;
#endif
  }
  for (size_t pc = 0;; pc++) {
    const Ins *in = &f->code[pc];
    V v;
    switch (in->op) {
    case OP_CONST:
      DEF(in->d); r[in->d] = f->consts[in->a]; v_dup(r[in->d]);
      break;
    case OP_DUP:
      DUPR(in->a); v_dup(r[in->a]);
      break;
    case OP_DROP:
      TAKE(in->a); v_drop(r[in->a]);
      break;
    case OP_DROP_REUSE:
      TAKE(in->a); v = drop_reuse(r[in->a]);
      DEF(in->d); r[in->d] = v;
      break;
    case OP_LIST: {
      V tok = NOTOK;
      if (in->a != NOREG) { TAKE(in->a); tok = r[in->a]; }
      for (uint16_t i = 0; i < in->c; i++) TAKE(in->b + i);
      v = p_list(tok, &r[in->b], in->c);
      DEF(in->d); r[in->d] = v;
      break;
    }
    case OP_ADD:
      TAKE(in->a); TAKE(in->b); v = p_add(r[in->a], r[in->b]);
      DEF(in->d); r[in->d] = v;
      break;
    case OP_REV:
      TAKE(in->a); v = p_rev(r[in->a]);
      DEF(in->d); r[in->d] = v;
      break;
    case OP_LEN:
      BORROW(in->a); v = p_len(r[in->a]);
      DEF(in->d); r[in->d] = v;
      break;
    case OP_EACH:
      BORROW(in->a); TAKE(in->b); v = p_each(r[in->a], r[in->b]);
      DEF(in->d); r[in->d] = v;
      break;
    case OP_CALL: {
      BORROW(in->a);
      const Fn *g = fn_of(r[in->a]);
      if (in->c != g->nparams) die("call: wrong number of arguments");
      for (uint16_t i = 0; i < in->c; i++) {
        if (g->borrowed >> i & 1) BORROW(in->b + i); else TAKE(in->b + i);
      }
      v = vm_call(g, &r[in->b]);
      DEF(in->d); r[in->d] = v;
      break;
    }
    case OP_RET:
      TAKE(in->a);
#if VM_CHECK
      for (unsigned i = 0; i < f->nregs; i++)
        if (own[i]) chk_fail(f, pc, i, "still owns a ref at return (leak)");
#endif
      return r[in->a];
    default:
      die("bad opcode");
    }
  }
}

// ======================================================================= tests

static void print_v(V v) {
  if (is_num(v)) { printf("%g", num(v)); return; }
  H *h = ptr(v);
  if (h->type == T_FN) { printf("<%s>", ((FnObj *)h)->fn->name); return; }
  printf("⟨");
  for (uint64_t i = 0; i < h->len; i++) { if (i) printf(", "); print_v(vals(h)[i]); }
  printf("⟩");
}

// {𝕩 + ⌽𝕩}: ⌽ runs first, so the left 𝕩 is the last use
static const Ins f_code[] = {
  {OP_DUP, .a = 0},                // dup x
  {OP_REV, .d = 1, .a = 0},        // t = rev x       rc(x)=2: allocates
  {OP_ADD, .d = 2, .a = 0, .b = 1},// r = add x, t    rc(x)=1: in place
  {OP_RET, .a = 2},
};
static const Fn f_fn = {"{𝕩+⌽𝕩}", f_code, NULL, 3, 1, 0};

// {𝕩+1}
static V g_k[1];
static const Ins g_code[] = {
  {OP_CONST, .d = 1, .a = 0},
  {OP_ADD, .d = 2, .a = 0, .b = 1},
  {OP_RET, .a = 2},
};
static const Fn g_fn = {"{𝕩+1}", g_code, g_k, 3, 1, 0};
static FnObj g_obj = {{.type = T_FN, .flags = F_STATIC}, &g_fn};

// {𝕩+1}¨: unique 𝕩, so results are written into its cells
static V e_k[1];
static const Ins e_code[] = {
  {OP_CONST, .d = 1, .a = 0},       // g (static: dup/drop are no-ops)
  {OP_EACH, .d = 2, .a = 1, .b = 0},
  {OP_DROP, .a = 1},
  {OP_RET, .a = 2},
};
static const Fn e_fn = {"{𝕩+1}¨", e_code, e_k, 3, 1, 0};

// {⟨≠𝕩, 0⟩}: 𝕩 dies after ≠, so the list reuses its block
static V h_k[1];
static const Ins h_code[] = {
  {OP_LEN, .d = 1, .a = 0},                   // n = len x   (borrows)
  {OP_CONST, .d = 2, .a = 0},
  {OP_DROP_REUSE, .d = 3, .a = 0},            // tok = drop_reuse x
  {OP_LIST, .d = 4, .a = 3, .b = 1, .c = 2},  // r = alloc_at tok, [n, 0]
  {OP_RET, .a = 4},
};
static const Fn h_fn = {"{⟨≠𝕩,0⟩}", h_code, h_k, 5, 1, 0};

static void run(const Fn *f) {
  V xs[3] = {mk_num(1), mk_num(2), mk_num(3)};
  V x = p_list(NOTOK, xs, 3);
  V y = vm_call(f, &x);
  printf("%-12s ⟨1, 2, 3⟩ → ", f->name);
  print_v(y);
  printf("\n");
  v_drop(y);
}

int main(void) {
  g_k[0] = mk_num(1);
  e_k[0] = mk_ptr(&g_obj.h);
  h_k[0] = mk_num(0);

  run(&f_fn);
  run(&e_fn);
  run(&h_fn);

  printf("reused blocks: %ld\n", reused);
  if (live_objs) { fprintf(stderr, "vm: %ld objects leaked\n", live_objs); return 1; }
  printf("rc balance ok\n");
  return 0;
}
