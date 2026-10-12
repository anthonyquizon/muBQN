// test/hand_main.c: the C side of test/hand.bqn, the differential tests of
// the hand-written VM. It includes src/vm.aq.c and drives it through a small
// API, so vm.aq.c can keep its own names for everything else.
//
// vm.aq.c must provide:
//   V, is_num(v), num(v), mk_num(d), is_chr(v), chr(v), mk_chr(c), NONE
//   V t_mkarr(uint8_t rank, const uint64_t *shape, V *elems)
//       a new array holding elems, which it takes ownership of
//   int t_isarr(V v); uint8_t t_rank(V a); const uint64_t *t_shape(V a);
//   uint64_t t_len(V a); V t_get(V a, uint64_t i)    (borrowed, not dup'd)
//   void v_drop(V v)
//   V t_call(const char *src, V w, V x)
//       run the primitive spelled src (such as "+" or "+´") on w and x,
//       which it consumes; w is NONE when called monadically
//   long t_live(void)   heap objects currently allocated (0 until you count)
//   jmp_buf *err_jmp; char err_msg[256]
//       vm_error writes its message to err_msg and longjmps to *err_jmp
// and must not define main when HAND_TEST is defined.
//
// Protocol, one case per line on stdin:
//   <src> <argument count> <arguments...>
// answered by "ok <value>" or "err <message>", prefixed with "leak <n> "
// if a successful case left n more objects alive than it started with.
// Values are space-separated tokens: n<number>, c<code point>, or
// a <rank> <shape...> <elements...>, as in src/vm.c's PRIM_TEST harness.

#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../src/vm.aq.c"

static void fail(const char *msg) {
  snprintf(err_msg, 256, "harness: %s", msg);
  longjmp(*err_jmp, 1);
}

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
static void ser(Buf *b, V v) {
  char t[64];
  if (is_num(v)) { snprintf(t, sizeof t, "n%.17g", num(v)); put(b, t); }
  else if (is_chr(v)) { snprintf(t, sizeof t, "c%u", (unsigned)chr(v)); put(b, t); }
  else if (t_isarr(v)) {
    snprintf(t, sizeof t, "a %d", t_rank(v)); put(b, t);
    for (int i = 0; i < t_rank(v); i++) {
      snprintf(t, sizeof t, " %llu", (unsigned long long)t_shape(v)[i]); put(b, t);
    }
    for (uint64_t i = 0; i < t_len(v); i++) { put(b, " "); ser(b, t_get(v, i)); }
  }
  else fail("result is not a number, character or array");
}

static char *tok_p;
static char *tok(void) {
  while (*tok_p == ' ') tok_p++;
  if (!*tok_p) fail("unexpected end of input");
  char *s = tok_p;
  while (*tok_p && *tok_p != ' ') tok_p++;
  if (*tok_p) *tok_p++ = 0;
  return s;
}
static V deser(void) {
  char *t = tok();
  if (t[0] == 'n') return mk_num(strtod(t + 1, NULL));
  if (t[0] == 'c') return mk_chr((uint32_t)strtoul(t + 1, NULL, 10));
  if (t[0] != 'a') fail("bad token");
  int rank = atoi(tok());
  uint64_t shape[256], len = 1;
  for (int i = 0; i < rank; i++) len *= shape[i] = strtoull(tok(), NULL, 10);
  V *elems = malloc((len ? len : 1) * sizeof(V));
  for (uint64_t i = 0; i < len; i++) elems[i] = deser();
  V a = t_mkarr((uint8_t)rank, shape, elems);
  free(elems);
  return a;
}

int main(void) {
  static char line[1 << 20];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\n")] = 0;
    if (!*line) continue;
    jmp_buf jb;
    err_jmp = &jb;
    if (setjmp(jb)) { printf("err %s\n", err_msg); fflush(stdout); continue; }
    long live = t_live();
    tok_p = line;
    char *src = tok();
    int nargs = atoi(tok());
    V x = deser(), w = NONE;
    if (nargs == 2) { w = x; x = deser(); }
    V r = t_call(src, w, x);
    Buf b = {0};
    ser(&b, r);
    v_drop(r);
    long leaked = t_live() - live;
    if (leaked) printf("leak %ld ", leaked);
    printf("ok %s\n", b.p);
    fflush(stdout);
    free(b.p);
  }
  return 0;
}
