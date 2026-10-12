// vm.c: muBQN. All hand-written C lives in this one file (see docs/design.md).
//
// Sections, in order:
//   runtime      errors, values, heap objects, reference counts, reuse tokens
//   functions    function objects, calls, and the combinators ∘ ○ ⊸ ⟜ ˜ ˙ ⊘ ◶ ⍟
//   arrays       construction, element access, comparison
//   basis        the operations of src/k.bqn, as b_x(w, x) and bm_x(f, w, x)
//   generated    gen/prims.c, compiled from src/prims.bqn by src/c.bqn
//   interpreter  milestone 4
//   main         -DPRIM_TEST builds the differential test harness instead
//
// Milestone 1: generated code does no reference counting, so nothing is freed
// and no basis operation writes into its arguments.
//
// Build: cc -std=c11 -O2 src/vm.c -o vm -lm
// Test:  bqn test/emit.bqn

#include <math.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Runtime and basis functions exist for generated code, which may not call
// all of them yet.
#pragma GCC diagnostic ignored "-Wunused-function"

// ===================================================================== runtime

// ---- errors. With a handler set (the test harness), an error longjmps to
// it; otherwise it ends the process.
static jmp_buf *err_jmp;
static char err_msg[512];
_Noreturn static void vm_error(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(err_msg, sizeof err_msg, fmt, ap);
  va_end(ap);
  if (err_jmp) longjmp(*err_jmp, 1);
  fprintf(stderr, "vm: %s\n", err_msg);
  exit(1);
}

// ---- values: NaN-boxed. Numbers are plain doubles (NaNs canonicalised);
// pointers, characters and NONE live in negative quiet-NaN space above every
// real double.
typedef uint64_t B;
#define TAG_MASK 0xFFFF000000000000ull
#define TAG_PTR  0xFFF9000000000000ull
#define TAG_CHR  0xFFFA000000000000ull
#define NONE     0xFFFB000000000000ull   // no left argument
#define NOTOK    TAG_PTR                 // null pointer: "no reuse token"

static inline int is_num(B v) { return v < TAG_PTR; }
static inline int is_ptr(B v) { return (v & TAG_MASK) == TAG_PTR; }
static inline int is_chr(B v) { return (v & TAG_MASK) == TAG_CHR; }
static inline double num(B v) { double d; memcpy(&d, &v, 8); return d; }
static inline uint32_t chr(B v) { return (uint32_t)v; }
static inline B mk_num(double d) {
  if (d != d) return 0x7FF8000000000000ull;
  B v; memcpy(&v, &d, 8); return v;
}
static inline B mk_chr(uint32_t c) { return TAG_CHR | c; }
#define N(d) mk_num(d)
#define C(c) mk_chr(c)

// ---- heap objects: header, then shape[rank], then len 8-byte elements.
// T_F64 elements are doubles, T_VAL elements are B; a number's B bits are its
// double bits, so copying code treats them alike.
enum { T_F64, T_VAL, T_FN, T_MARK, T_TOK };
enum { F_STATIC = 1 };  // static objects: never reference counted

typedef struct H {
  int32_t rc;
  uint8_t type, rank, flags, _pad;
  uint64_t len;  // element count (environment size for T_FN)
  uint64_t cap;  // block size in bytes, for reuse
} H;

static inline H *ptr(B v) { return (H *)(uintptr_t)(v & ~TAG_MASK); }
static inline B mk_ptr(H *h) { return (B)(uintptr_t)h | TAG_PTR; }
static inline uint64_t *shp(H *h) { return (uint64_t *)(h + 1); }
static inline B *vals(H *h) { return (B *)(shp(h) + h->rank); }
static inline double *f64s(H *h) { return (double *)(shp(h) + h->rank); }
static inline int unique(H *h) { return h->rc == 1 && !(h->flags & F_STATIC); }
static inline int is_type(B v, int t) { return is_ptr(v) && ptr(v)->type == t; }
static inline int is_arr(B v) { return is_type(v, T_F64) || is_type(v, T_VAL); }

static long live_objs;  // must be 0 at exit once reference counting is on
static long reused;     // stats: blocks recycled through reuse tokens

static void h_free(H *h);

static inline void v_dup(B v) {
  if (!is_ptr(v) || v == NOTOK) return;
  H *h = ptr(v);
  if (!(h->flags & F_STATIC)) h->rc++;
}
static inline void v_drop(B v) {
  if (!is_ptr(v) || v == NOTOK) return;
  H *h = ptr(v);
  if (!(h->flags & F_STATIC) && --h->rc == 0) h_free(h);
}

static void h_drop_children(H *h) {
  if (h->type == T_VAL || h->type == T_FN)
    for (uint64_t i = 0; i < h->len; i++) v_drop(vals(h)[i]);
}
static void h_free(H *h) { h_drop_children(h); live_objs--; free(h); }

static H *h_alloc(uint8_t type, uint8_t rank, uint64_t len) {
  size_t bytes = sizeof(H) + (rank + len) * 8;
  H *h = malloc(bytes);
  if (!h) vm_error("out of memory");
  *h = (H){.rc = 1, .type = type, .rank = rank, .len = len, .cap = bytes};
  live_objs++;
  return h;
}

// ---- reuse tokens. drop_reuse consumes v; if it held the only reference,
// its children are dropped and its block becomes a token for alloc_at.
static B drop_reuse(B v) {
  if (!is_ptr(v)) return NOTOK;
  H *h = ptr(v);
  if (h->flags & F_STATIC) return NOTOK;
  if (h->rc != 1) { h->rc--; return NOTOK; }
  h_drop_children(h);
  h->type = T_TOK;  // a token dropped unused is just freed
  return v;
}
static H *alloc_at(B tok, uint8_t type, uint8_t rank, uint64_t len) {
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

// =================================================================== functions

// A function object holds a C function and an environment: captured values
// for a block, operands for a derived function. Data called as a function
// returns itself, as in BQN.
typedef B (*FnP)(B *e, B w, B x);
typedef struct { H h; FnP fn; } FnH;
static inline B *env(H *h) { return (B *)((FnH *)h + 1); }

static B mk_fn(FnP f, int n, ...) {
  FnH *o = malloc(sizeof(FnH) + n * 8);
  if (!o) vm_error("out of memory");
  o->h = (H){.rc = 1, .type = T_FN, .len = n, .cap = sizeof(FnH) + n * 8};
  o->fn = f;
  live_objs++;
  va_list ap;
  va_start(ap, n);
  for (int i = 0; i < n; i++) env(&o->h)[i] = va_arg(ap, B);
  va_end(ap);
  return mk_ptr(&o->h);
}
static B fn_static(FnP f) {
  B v = mk_fn(f, 0);
  ptr(v)->flags |= F_STATIC;
  live_objs--;
  return v;
}
static B call(B f, B w, B x) {
  if (!is_type(f, T_FN)) return f;
  return ((FnH *)ptr(f))->fn(env(ptr(f)), w, x);
}
#define OR_X(w, x) ((w) == NONE ? (x) : (w))

static B D_atop(B *e, B w, B x) { return call(e[0], NONE, call(e[1], w, x)); }
static B D_fork(B *e, B w, B x) {
  B r = call(e[2], w, x);
  B l = call(e[0], w, x);
  return call(e[1], l, r);
}
static B D_atop2(B *e, B w, B x) { return call(e[0], NONE, call(e[1], w, x)); }  // ∘
static B D_over(B *e, B w, B x) {                                               // ○
  B gx = call(e[1], NONE, x);
  return call(e[0], w == NONE ? NONE : call(e[1], NONE, w), gx);
}
static B D_before(B *e, B w, B x) { return call(e[1], call(e[0], NONE, OR_X(w, x)), x); }  // ⊸
static B D_after(B *e, B w, B x) { return call(e[0], OR_X(w, x), call(e[1], NONE, x)); }   // ⟜
static B D_swap(B *e, B w, B x) { return call(e[0], x, OR_X(w, x)); }                      // ˜
static B D_const(B *e, B w, B x) { (void)w; (void)x; return e[0]; }                        // ˙
static B D_valences(B *e, B w, B x) { return w == NONE ? call(e[0], NONE, x) : call(e[1], w, x); }  // ⊘
static B list_get(B a, uint64_t i);
static uint64_t count(H *h);
static B D_choose(B *e, B w, B x) {                                             // ◶
  B i = call(e[0], w, x);
  if (!is_num(i) || !is_arr(e[1])) vm_error("◶: 𝔽 must give an index into the list 𝕘");
  double d = num(i);
  if (d != floor(d) || d < 0 || d >= (double)count(ptr(e[1]))) vm_error("◶: index out of range");
  return call(list_get(e[1], (uint64_t)d), w, x);
}
static B D_repeat(B *e, B w, B x) {                                             // ⍟ with a natural count
  B n = call(e[1], w, x);
  if (!is_num(n) || num(n) < 0 || num(n) != floor(num(n))) vm_error("⍟: only natural repetition counts are supported");
  for (double i = 0; i < num(n); i++) x = call(e[0], w, x);
  return x;
}
static B F_right(B *e, B w, B x) { (void)e; (void)w; return x; }
static B F_left(B *e, B w, B x) { (void)e; return OR_X(w, x); }
static B p_assert(B w, B x);
static B F_assert(B *e, B w, B x) { (void)e; return p_assert(w, x); }
static B P_right, P_left, P_assert;

// ====================================================================== arrays

static uint64_t count(H *h) {
  uint64_t n = 1;
  for (int i = 0; i < h->rank; i++) n *= shp(h)[i];
  return n;
}
static H *new_arr(uint8_t type, uint8_t rank, const uint64_t *shape) {
  uint64_t n = 1;
  for (int i = 0; i < rank; i++) n *= shape[i];
  H *h = h_alloc(type, rank, n);
  memcpy(shp(h), shape, rank * 8);
  return h;
}
static H *new_list(uint8_t type, uint64_t n) { return new_arr(type, 1, &n); }
static B elem(H *h, uint64_t i) {
  return h->type == T_F64 ? mk_num(f64s(h)[i]) : vals(h)[i];
}
static B list_get(B a, uint64_t i) {
  if (!is_arr(a) || i >= ptr(a)->len) vm_error("index out of range");
  return elem(ptr(a), i);
}
// T_VAL array whose elements are all numbers → T_F64, in place
static B squeeze(H *h) {
  if (h->type != T_VAL) return mk_ptr(h);
  for (uint64_t i = 0; i < h->len; i++) if (!is_num(vals(h)[i])) return mk_ptr(h);
  h->type = T_F64;
  for (uint64_t i = 0; i < h->len; i++) f64s(h)[i] = num(vals(h)[i]);
  return mk_ptr(h);
}
static B mk_list(int n, const B *xs) {
  H *h = new_list(T_VAL, n);
  if (n) memcpy(vals(h), xs, n * 8);
  return squeeze(h);
}
static void need_list(B a, int n) {
  if (!is_arr(a) || ptr(a)->rank != 1 || ptr(a)->len != (uint64_t)n)
    vm_error("destructuring needs a list of %d elements", n);
}
static B str_lit(const uint32_t *cs, uint64_t n) {
  H *h = new_list(T_VAL, n);
  for (uint64_t i = 0; i < n; i++) vals(h)[i] = mk_chr(cs[i]);
  return mk_ptr(h);
}
static int truth(B v) {
  if (v == N(0)) return 0;
  if (v == N(1)) return 1;
  vm_error("Expected boolean");
}
static B vm_nomatch(void) { vm_error("No header matched arguments"); }
static B p_assert(B w, B x) {
  if (x == N(1)) return x;
  if (w == NONE) vm_error("Assertion error");
  char buf[256]; size_t k = 0;
  if (is_arr(w))
    for (uint64_t i = 0; i < ptr(w)->len && k + 4 < sizeof buf; i++) {
      B c = elem(ptr(w), i);
      uint32_t u = is_chr(c) ? chr(c) : '?';
      if (u < 0x80) buf[k++] = (char)u;
      else if (u < 0x800) { buf[k++] = 0xC0 | u >> 6; buf[k++] = 0x80 | (u & 63); }
      else if (u < 0x10000) { buf[k++] = 0xE0 | u >> 12; buf[k++] = 0x80 | (u >> 6 & 63); buf[k++] = 0x80 | (u & 63); }
      else { buf[k++] = 0xF0 | u >> 18; buf[k++] = 0x80 | (u >> 12 & 63); buf[k++] = 0x80 | (u >> 6 & 63); buf[k++] = 0x80 | (u & 63); }
    }
  buf[k] = 0;
  vm_error("%s", buf);
}

// ≡: numbers by value (so NaN doesn't match itself, as in CBQN), characters
// by code, arrays by shape and elements, anything else by identity
static int match(B a, B b) {
  if (is_num(a) || is_num(b)) return is_num(a) && is_num(b) && num(a) == num(b);
  if (!is_arr(a) || !is_arr(b)) return a == b;
  H *x = ptr(a), *y = ptr(b);
  if (x->rank != y->rank || memcmp(shp(x), shp(y), x->rank * 8)) return 0;
  for (uint64_t i = 0; i < x->len; i++) if (!match(elem(x, i), elem(y, i))) return 0;
  return 1;
}
// BQN's total order: numbers (NaN last), then characters; arrays compare by
// ravel, then by length, rank and shape; an atom is a unit array that comes
// before an equal array
static int cmp(B a, B b) {
  int aa = is_arr(a), ba = is_arr(b);
  if (!aa && !ba) {
    int ta = is_num(a) ? 0 : is_chr(a) ? 1 : 2, tb = is_num(b) ? 0 : is_chr(b) ? 1 : 2;
    if (ta != tb) return ta < tb ? -1 : 1;
    if (ta == 0) {
      double x = num(a), y = num(b);
      if (x != x || y != y) return (x != x) - (y != y);
      return (x > y) - (x < y);
    }
    if (ta == 1) return (chr(a) > chr(b)) - (chr(a) < chr(b));
    return (a > b) - (a < b);
  }
  uint64_t na = aa ? ptr(a)->len : 1, nb = ba ? ptr(b)->len : 1;
  for (uint64_t i = 0; i < na && i < nb; i++) {
    int c = cmp(aa ? elem(ptr(a), i) : a, ba ? elem(ptr(b), i) : b);
    if (c) return c;
  }
  if (na != nb) return na < nb ? -1 : 1;
  int ra = aa ? ptr(a)->rank : 0, rb = ba ? ptr(b)->rank : 0;
  if (ra != rb) return ra < rb ? -1 : 1;
  for (int i = 0; i < ra; i++)
    if (shp(ptr(a))[i] != shp(ptr(b))[i]) return shp(ptr(a))[i] < shp(ptr(b))[i] ? -1 : 1;
  return 0;
}

// ======================================================================= basis
// The operations of src/k.bqn, with the same contracts. Each checks its
// arguments and calls vm_error when they don't hold. w is NONE for monadic
// calls. Results never share memory with arguments.

static H *need_arr(B v, const char *who) {
  if (!is_arr(v)) vm_error("%s: 𝕩 must be an array", who);
  return ptr(v);
}
static H *need_list1(B v, const char *who) {
  if (!is_arr(v) || ptr(v)->rank != 1) vm_error("%s: argument must be a list", who);
  return ptr(v);
}
static int is_flat(B v) {
  if (!is_arr(v) || ptr(v)->rank != 1) return 0;
  H *h = ptr(v);
  if (h->type == T_F64) return 1;
  for (uint64_t i = 0; i < h->len; i++) if (!is_num(vals(h)[i])) return 0;
  return 1;
}
static double nat(B v, const char *who) {
  if (!is_num(v) || num(v) < 0 || num(v) != floor(num(v)) || num(v) > 9007199254740992.0)
    vm_error("%s: expected a natural number", who);
  return num(v);
}
static int is_int(B v) { return is_num(v) && num(v) == floor(num(v)) && fabs(num(v)) < 9007199254740992.0; }
static B copy_list(H *src, uint64_t from, uint64_t n) {
  H *r = new_list(src->type, n);
  memcpy(vals(r), vals(src) + from, n * 8);
  return mk_ptr(r);
}

// ---- queries
static B b_isarr(B w, B x) { (void)w; return N(is_arr(x)); }
static B b_shape(B w, B x) {
  (void)w;
  if (!is_arr(x)) return mk_list(0, NULL);
  H *h = ptr(x), *r = new_list(T_F64, h->rank);
  for (int i = 0; i < h->rank; i++) f64s(r)[i] = (double)shp(h)[i];
  return mk_ptr(r);
}
static B b_len(B w, B x) {
  (void)w;
  return N(is_arr(x) && ptr(x)->rank ? (double)shp(ptr(x))[0] : 1);
}
static B b_count(B w, B x) { (void)w; return N(is_arr(x) ? (double)ptr(x)->len : 1); }
static B b_type(B w, B x) {
  (void)w;
  return N(is_arr(x) ? 0 : is_num(x) ? 1 : is_chr(x) ? 2 : is_type(x, T_FN) ? 3 : 6);
}
static B b_flat(B w, B x) { (void)w; return N(is_arr(x) && ptr(x)->rank == 1 && ptr(x)->type == T_F64); }
static B fill_of(B v) {
  if (is_num(v)) return N(0);
  if (is_chr(v)) return C(' ');
  if (!is_arr(v)) vm_error("k.Fill: no fill for this element");
  H *h = ptr(v), *r = new_arr(T_VAL, h->rank, shp(h));
  for (uint64_t i = 0; i < h->len; i++) vals(r)[i] = fill_of(elem(h, i));
  return squeeze(r);
}
static B b_fill(B w, B x) {
  (void)w;
  H *h = need_list1(x, "k.Fill");
  if (h->type == T_F64) return N(0);
  if (!h->len) vm_error("k.Fill: an empty generic list has no known fill");
  return fill_of(vals(h)[0]);
}
static B b_same(B w, B x) { return N(match(w, x)); }
static B b_match(B w, B x) { return N(match(w, x)); }

// ---- construction
static B b_reshape(B w, B x) {
  H *s = need_list1(w, "k.Reshape"), *d = need_list1(x, "k.Reshape");
  if (s->len > 255) vm_error("k.Reshape: rank too large");
  uint64_t shape[256], n = 1;
  for (uint64_t i = 0; i < s->len; i++) { shape[i] = (uint64_t)nat(elem(s, i), "k.Reshape"); n *= shape[i]; }
  if (n != d->len) vm_error("k.Reshape: 𝕩 must have exactly ×´𝕨 elements");
  H *r = new_arr(d->type, (uint8_t)s->len, shape);
  memcpy(vals(r), vals(d), n * 8);
  return mk_ptr(r);
}
static B b_deshape(B w, B x) {
  (void)w;
  H *h = need_arr(x, "k.Deshape");
  return copy_list(h, 0, h->len);
}
static B b_range(B w, B x) {
  (void)w;
  uint64_t n = (uint64_t)nat(x, "k.Range");
  H *r = new_list(T_F64, n);
  for (uint64_t i = 0; i < n; i++) f64s(r)[i] = (double)i;
  return mk_ptr(r);
}
static B b_cat(B w, B x) {
  (void)w;
  H *h = need_list1(x, "k.Cat");
  uint64_t n = 0; int all_f64 = 1;
  for (uint64_t i = 0; i < h->len; i++) {
    H *p = need_list1(elem(h, i), "k.Cat");
    n += p->len; all_f64 &= p->type == T_F64;
  }
  H *r = new_list(all_f64 ? T_F64 : T_VAL, n);
  uint64_t k = 0;
  for (uint64_t i = 0; i < h->len; i++) {
    H *p = ptr(elem(h, i));
    for (uint64_t j = 0; j < p->len; j++, k++) {
      if (all_f64) f64s(r)[k] = f64s(p)[j];
      else vals(r)[k] = elem(p, j);
    }
  }
  return mk_ptr(r);
}
static B b_slice(B w, B x) {
  need_list(w, 2);
  H *h = need_list1(x, "k.Slice");
  uint64_t s = (uint64_t)nat(list_get(w, 0), "k.Slice"), l = (uint64_t)nat(list_get(w, 1), "k.Slice");
  if (s + l > h->len) vm_error("k.Slice: out of range");
  return copy_list(h, s, l);
}
static uint64_t index_into(B i, uint64_t len, const char *who) {
  if (!is_int(i)) vm_error("%s: index must be an integer", who);
  double d = num(i);
  if (d < -(double)len || d >= (double)len) vm_error("%s: index out of bounds", who);
  return (uint64_t)(d < 0 ? d + (double)len : d);
}
static B b_pick(B w, B x) {
  H *h = need_list1(x, "k.Pick");
  return elem(h, index_into(w, h->len, "k.Pick"));
}

// ---- arithmetic on numbers and flat lists
enum { O_ADD, O_SUB, O_MUL, O_DIV, O_MOD, O_MIN, O_MAX, O_EQ, O_NE, O_LT, O_LE, O_GT, O_GE };
static inline double op2(int op, double a, double b) {
  switch (op) {
    case O_ADD: return a + b;
    case O_SUB: return a - b;
    case O_MUL: return a * b;
    case O_DIV: return a / b;
    case O_MOD: {                              // 𝕨|𝕩, rounding as CBQN does
      double r = fmod(b, a);
      return r != 0 && (r < 0) != (a < 0) ? r + a : r;
    }
    case O_MIN: return a < b ? a : b;
    case O_MAX: return a > b ? a : b;
    case O_EQ: return a == b;
    case O_NE: return a != b;
    case O_LT: return a < b;
    case O_LE: return a <= b;
    case O_GT: return a > b;
    default: return a >= b;
  }
}
static B arith(int op, B w, B x) {
  if (is_num(w) && is_num(x)) return N(op2(op, num(w), num(x)));
  if (!(is_num(w) || is_flat(w)) || !(is_num(x) || is_flat(x))) vm_error("k: arithmetic on non-numbers");
  uint64_t n = is_num(w) ? ptr(x)->len : ptr(w)->len;
  if (!is_num(w) && !is_num(x) && ptr(x)->len != n) vm_error("k: length mismatch");
  H *r = new_list(T_F64, n);
  double *d = f64s(r);
  for (uint64_t i = 0; i < n; i++) {
    double a = is_num(w) ? num(w) : num(elem(ptr(w), i));
    double b = is_num(x) ? num(x) : num(elem(ptr(x), i));
    d[i] = op2(op, a, b);
  }
  return mk_ptr(r);
}
#define ARITH(name, op) static B b_##name(B w, B x) { return arith(op, w, x); }
ARITH(add, O_ADD) ARITH(sub, O_SUB) ARITH(mul, O_MUL) ARITH(div, O_DIV) ARITH(mod, O_MOD)
ARITH(min, O_MIN) ARITH(max, O_MAX) ARITH(eq, O_EQ) ARITH(ne, O_NE)
ARITH(lt, O_LT) ARITH(le, O_LE) ARITH(gt, O_GT) ARITH(ge, O_GE)
#undef ARITH
static B arith1(double (*f)(double), B x) {
  if (is_num(x)) return N(f(num(x)));
  if (!is_flat(x)) vm_error("k: arithmetic on non-numbers");
  H *h = ptr(x), *r = new_list(T_F64, h->len);
  for (uint64_t i = 0; i < h->len; i++) f64s(r)[i] = f(num(elem(h, i)));
  return mk_ptr(r);
}
static B b_floor(B w, B x) { (void)w; return arith1(floor, x); }
static B b_abs(B w, B x) { (void)w; return arith1(fabs, x); }

// ---- folds (right to left, as BQN's ´) and scans over flat lists
static H *need_flat(B x, const char *who) {
  if (!is_flat(x)) vm_error("%s: needs a flat list", who);
  return ptr(x);
}
#define FOLD(name, init, OP)                                                   \
  static B b_##name(B w, B x) {                                                \
    (void)w;                                                                   \
    H *h = need_flat(x, "k." #name);                                           \
    if (!h->len) return N(init);                                               \
    double a = num(elem(h, h->len - 1));                                       \
    for (uint64_t i = h->len - 1; i-- > 0;) { double b = num(elem(h, i)); a = OP; } \
    return N(a);                                                               \
  }
FOLD(foldadd, 0, b + a)
FOLD(foldmul, 1, b * a)
FOLD(foldmax, -INFINITY, (b > a ? b : a))
FOLD(foldmin, INFINITY, (b < a ? b : a))
#undef FOLD
static B scan(int max, B x) {
  H *h = need_flat(x, "k.Scan"), *r = new_list(T_F64, h->len);
  for (uint64_t i = 0; i < h->len; i++) {
    double b = num(elem(h, i));
    f64s(r)[i] = i == 0 ? b : max ? (f64s(r)[i-1] > b ? f64s(r)[i-1] : b) : f64s(r)[i-1] + b;
  }
  return mk_ptr(r);
}
static B b_scanadd(B w, B x) { (void)w; return scan(0, x); }
static B b_scanmax(B w, B x) { (void)w; return scan(1, x); }

// ---- selection
static B b_gather(B w, B x) {
  if (!is_flat(w)) vm_error("k.Gather: 𝕨 must be a flat list");
  H *ix = ptr(w), *s = need_list1(x, "k.Gather"), *r = new_list(s->type, ix->len);
  for (uint64_t i = 0; i < ix->len; i++)
    vals(r)[i] = vals(s)[index_into(elem(ix, i), s->len, "k.Gather")];
  return mk_ptr(r);
}
static B b_scatter(B w, B x) {
  need_list(w, 2);
  B iv = list_get(w, 0), vv = list_get(w, 1);
  H *s = need_list1(x, "k.Scatter");
  if (!is_flat(iv)) vm_error("k.Scatter: indices must be a flat list");
  H *ix = ptr(iv), *v = need_list1(vv, "k.Scatter");
  if (ix->len != v->len) vm_error("k.Scatter: indices and values must have equal length");
  H *r = new_list(T_VAL, s->len);
  for (uint64_t i = 0; i < s->len; i++) vals(r)[i] = elem(s, i);
  for (uint64_t i = 0; i < ix->len; i++)
    vals(r)[index_into(elem(ix, i), s->len, "k.Scatter")] = elem(v, i);
  return squeeze(r);
}
static B b_compress(B w, B x) {
  H *b = need_flat(w, "k.Compress"), *s = need_list1(x, "k.Compress");
  if (b->len != s->len) vm_error("k.Compress: 𝕩 must be a list as long as 𝕨");
  uint64_t n = 0;
  for (uint64_t i = 0; i < b->len; i++) {
    double d = num(elem(b, i));
    if (d != 0 && d != 1) vm_error("k.Compress: 𝕨 must be boolean");
    n += d == 1;
  }
  H *r = new_list(s->type, n);
  for (uint64_t i = 0, k = 0; i < b->len; i++) if (num(elem(b, i)) == 1) vals(r)[k++] = vals(s)[i];
  return mk_ptr(r);
}
static B b_indices(B w, B x) {
  (void)w;
  H *c = need_flat(x, "k.Indices");
  uint64_t n = 0;
  for (uint64_t i = 0; i < c->len; i++) n += (uint64_t)nat(elem(c, i), "k.Indices");
  H *r = new_list(T_F64, n);
  for (uint64_t i = 0, k = 0; i < c->len; i++)
    for (uint64_t j = (uint64_t)num(elem(c, i)); j--;) f64s(r)[k++] = (double)i;
  return mk_ptr(r);
}

// ---- search and sort
static void merge_sort(uint64_t *ix, uint64_t *tmp, uint64_t n, H *h) {
  if (n < 2) return;
  uint64_t m = n / 2;
  merge_sort(ix, tmp, m, h);
  merge_sort(ix + m, tmp, n - m, h);
  uint64_t i = 0, j = m, k = 0;
  while (i < m && j < n) tmp[k++] = cmp(elem(h, ix[j]), elem(h, ix[i])) < 0 ? ix[j++] : ix[i++];
  while (i < m) tmp[k++] = ix[i++];
  while (j < n) tmp[k++] = ix[j++];
  memcpy(ix, tmp, n * 8);
}
static B b_grade(B w, B x) {
  (void)w;
  H *h = need_list1(x, "k.Grade");
  uint64_t *ix = malloc(h->len * 8 + 1), *tmp = malloc(h->len * 8 + 1);
  for (uint64_t i = 0; i < h->len; i++) ix[i] = i;
  merge_sort(ix, tmp, h->len, h);
  H *r = new_list(T_F64, h->len);
  for (uint64_t i = 0; i < h->len; i++) f64s(r)[i] = (double)ix[i];
  free(ix); free(tmp);
  return mk_ptr(r);
}
static B b_indexof(B w, B x) {
  H *a = need_list1(w, "k.IndexOf"), *b = need_list1(x, "k.IndexOf");
  H *r = new_list(T_F64, b->len);
  for (uint64_t i = 0; i < b->len; i++) {
    uint64_t j = 0;
    B v = elem(b, i);
    while (j < a->len && !match(elem(a, j), v)) j++;
    f64s(r)[i] = (double)j;
  }
  return mk_ptr(r);
}
static B b_hist(B w, B x) {
  uint64_t n = (uint64_t)nat(w, "k.Hist");
  H *c = need_flat(x, "k.Hist"), *r = new_list(T_F64, n);
  for (uint64_t i = 0; i < n; i++) f64s(r)[i] = 0;
  for (uint64_t i = 0; i < c->len; i++) {
    double d = nat(elem(c, i), "k.Hist");
    if (d >= (double)n) vm_error("k.Hist: values must be below 𝕨");
    f64s(r)[(uint64_t)d]++;
  }
  return mk_ptr(r);
}

// ---- callbacks
static B bm_each(B f, B w, B x) {
  H *b = need_list1(x, "k._each");
  H *a = w == NONE ? NULL : need_list1(w, "k._each");
  if (a && a->len != b->len) vm_error("k._each: 𝕨 and 𝕩 must have equal length");
  H *r = new_list(T_VAL, b->len);
  for (uint64_t i = 0; i < b->len; i++) vals(r)[i] = call(f, a ? elem(a, i) : NONE, elem(b, i));
  return squeeze(r);
}
static B bm_fold(B f, B w, B x) {
  H *h = need_list1(x, "k._fold");
  uint64_t n = h->len;
  if (w == NONE && !n) vm_error("k._fold: empty 𝕩 needs 𝕨");
  B a = w == NONE ? elem(h, --n) : w;
  while (n--) a = call(f, elem(h, n), a);
  return a;
}
static B bm_scan(B f, B w, B x) {
  (void)w;
  H *h = need_list1(x, "k._scan"), *r = new_list(T_VAL, h->len);
  for (uint64_t i = 0; i < h->len; i++)
    vals(r)[i] = i == 0 ? elem(h, 0) : call(f, vals(r)[i-1], elem(h, i));
  return squeeze(r);
}

// ---- markers: opaque values that match only themselves, for ⌾
static B b_markers(B w, B x) {
  (void)w;
  uint64_t n = (uint64_t)nat(x, "k.Markers");
  H *r = new_list(T_VAL, n);
  for (uint64_t i = 0; i < n; i++) vals(r)[i] = mk_ptr(h_alloc(T_MARK, 0, 0));
  return mk_ptr(r);
}
static B b_ismarker(B w, B x) { (void)w; return N(is_type(x, T_MARK)); }

// ---- encodings. Nothing is stored compressed yet: Enc always answers
// "plain", which is always correct, and the constructors build plain lists.
static B S_plain;
static B b_enc(B w, B x) { (void)w; (void)x; return S_plain; }
static B b_parts(B w, B x) { (void)w; (void)x; vm_error("k.Parts: the list is not encoded"); }
static B b_sorted(B w, B x) { (void)w; (void)x; return N(0); }
static B b_mkconst(B w, B x) {
  (void)w;
  need_list(x, 2);
  B v = list_get(x, 0);
  uint64_t n = (uint64_t)nat(list_get(x, 1), "k.MkConst");
  H *r = new_list(T_VAL, n);
  for (uint64_t i = 0; i < n; i++) vals(r)[i] = v;
  return squeeze(r);
}
static B b_mkrange(B w, B x) {
  (void)w;
  need_list(x, 3);
  B s = list_get(x, 0), d = list_get(x, 1);
  if (!is_int(s) || !is_int(d)) vm_error("k.MkRange: s and d must be integers");
  uint64_t n = (uint64_t)nat(list_get(x, 2), "k.MkRange");
  if (n && !is_int(N(num(s) + num(d) * (double)(n - 1)))) vm_error("k.MkRange: elements must stay integers");
  H *r = new_list(T_F64, n);
  for (uint64_t i = 0; i < n; i++) f64s(r)[i] = num(s) + num(d) * (double)i;
  return mk_ptr(r);
}
static B b_mkruns(B w, B x) {
  (void)w;
  need_list(x, 2);
  H *v = need_list1(list_get(x, 0), "k.MkRuns"), *c = need_flat(list_get(x, 1), "k.MkRuns");
  if (v->len != c->len) vm_error("k.MkRuns: v and c must have equal length");
  uint64_t n = 0;
  for (uint64_t i = 0; i < c->len; i++) {
    double k = nat(elem(c, i), "k.MkRuns");
    if (k < 1) vm_error("k.MkRuns: counts must be at least 1");
    n += (uint64_t)k;
  }
  H *r = new_list(v->type, n);
  for (uint64_t i = 0, k = 0; i < c->len; i++)
    for (uint64_t j = (uint64_t)num(elem(c, i)); j--;) vals(r)[k++] = vals(v)[i];
  return mk_ptr(r);
}
static B b_mkdict(B w, B x) {
  (void)w;
  need_list(x, 2);
  B c = list_get(x, 0), d = list_get(x, 1);
  need_list1(d, "k.MkDict");
  if (!is_flat(c)) vm_error("k.MkDict: codes must be a flat list");
  for (uint64_t i = 0; i < ptr(c)->len; i++) {
    double k = nat(elem(ptr(c), i), "k.MkDict");
    if (k >= (double)ptr(d)->len) vm_error("k.MkDict: codes must index d");
  }
  return b_gather(c, d);
}

static void runtime_init(void) {
  S_plain = str_lit((const uint32_t[]){'p', 'l', 'a', 'i', 'n'}, 5);
  P_right = fn_static(F_right);
  P_left = fn_static(F_left);
  P_assert = fn_static(F_assert);
}

// =================================================================== generated

// Generated code jumps between bodies by label and may leave temporaries
// unused; neither is worth a warning.
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"
#ifdef GEN_FILE
#include GEN_FILE   // the tests build with extra definitions
#else
#include "gen/prims.c"
#endif
#pragma GCC diagnostic pop

// ================================================================= interpreter
// Milestone 4.

// ======================================================================== main

#ifdef PRIM_TEST

// Differential test harness: reads one case per line from stdin and prints
// one result per line. A case is an exported name, an argument count and the
// serialized arguments; a result is "ok <value>" or "err <message>".
//
// Serialization, as space-separated tokens:
//   n<number>   number, printed with %.17g (inf, -inf, nan)
//   c<code>     character
//   a <rank> <shape...> <elements...>
//   f, m        function, marker (output only)

typedef struct { char *p; size_t n, cap; } Buf;
static void put(Buf *b, const char *s) {
  size_t k = strlen(s);
  if (b->n + k + 1 > b->cap) {
    b->cap = 2 * (b->n + k + 1);
    b->p = realloc(b->p, b->cap);
  }
  memcpy(b->p + b->n, s, k + 1);
  b->n += k;
}
static void ser(Buf *b, B v) {
  char t[64];
  if (is_num(v)) { snprintf(t, sizeof t, "n%.17g", num(v)); put(b, t); }
  else if (is_chr(v)) { snprintf(t, sizeof t, "c%u", chr(v)); put(b, t); }
  else if (is_arr(v)) {
    H *h = ptr(v);
    snprintf(t, sizeof t, "a %d", h->rank); put(b, t);
    for (int i = 0; i < h->rank; i++) { snprintf(t, sizeof t, " %llu", (unsigned long long)shp(h)[i]); put(b, t); }
    for (uint64_t i = 0; i < h->len; i++) { put(b, " "); ser(b, elem(h, i)); }
  }
  else put(b, is_type(v, T_FN) ? "f" : "m");
}
static char *tok_p;
static char *tok(void) {
  while (*tok_p == ' ') tok_p++;
  if (!*tok_p) vm_error("harness: unexpected end of input");
  char *s = tok_p;
  while (*tok_p && *tok_p != ' ') tok_p++;
  if (*tok_p) *tok_p++ = 0;
  return s;
}
static B deser(void) {
  char *t = tok();
  if (t[0] == 'n') return N(strtod(t + 1, NULL));
  if (t[0] == 'c') return C((uint32_t)strtoul(t + 1, NULL, 10));
  if (t[0] != 'a') vm_error("harness: bad token %s", t);
  int rank = atoi(tok());
  uint64_t shape[256];
  for (int i = 0; i < rank; i++) shape[i] = strtoull(tok(), NULL, 10);
  H *h = new_arr(T_VAL, (uint8_t)rank, shape);
  for (uint64_t i = 0; i < h->len; i++) vals(h)[i] = deser();
  return squeeze(h);
}

int main(void) {
  runtime_init();
  gen_init();
  static char line[1 << 20];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\n")] = 0;
    if (!*line) continue;
    jmp_buf jb;
    err_jmp = &jb;
    if (setjmp(jb)) { printf("err %s\n", err_msg); fflush(stdout); continue; }
    tok_p = line;
    char *name = tok();
    B *fn = NULL;
    for (int i = 0; gen_exports[i].name; i++)
      if (!strcmp(gen_exports[i].name, name)) fn = gen_exports[i].val;
    if (!fn) vm_error("harness: no export named %s", name);
    int nargs = atoi(tok());
    B x = deser(), w = NONE;
    if (nargs == 2) { w = x; x = deser(); }
    B r = call(*fn, w, x);
    Buf b = {0};
    ser(&b, r);
    printf("ok %s\n", b.p);
    fflush(stdout);
    free(b.p);
  }
  return 0;
}

#else

int main(void) {
  runtime_init();
  gen_init();
  fputs("vm: interpreter not written yet (milestone 4); "
        "run test/emit.bqn for the compiled primitives\n", stderr);
  return 1;
}

#endif
