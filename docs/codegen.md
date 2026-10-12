# Primitive dialect to C: a worked example

How `src/c.bqn` turns dialect source (`src/prims.bqn`) into C
(`src/gen/prims.c`), and which parts of `src/vm.c` that C calls. The design
behind it is in [design.md](design.md#primitive-dialect).

## Overview

The C is not a glyph-by-glyph mapping onto functions that already exist in
`vm.c`. The primitives are written in BQN in `prims.bqn`, and each top-level
definition there becomes a **new** C function in `gen/prims.c`. That file is
`#include`d into `vm.c` at the "generated" section.

```
src/prims.bqn
  → dialect.bqn   glyphs rewritten to names (⌽ → Reverse, ¨ → _each),
                  dependency rule checked
  → c.bqn         Lex, Parse, Gen
  → src/gen/prims.c   one F_<name> function per definition,
                      #include'd by vm.c
```

Each definition also gets a global holding it as a function value, so that it
can be passed as an operand:

```c
g_reverse = fn_static(F_reverse);
```

## What generated code calls

| Dialect source | Generated C | Defined in |
|---|---|---|
| `k.Sub`, `k.Len`, `k.Reshape`, … | `b_sub`, `b_len`, `b_reshape`, … | `vm.c`, basis section |
| `k._each`, `k._fold`, `k._scan` | `bm_each`, `bm_fold`, `bm_scan` | `vm.c`, basis section |
| An earlier dialect definition (`RankOf`, `SelCells`) | `F_rankof(...)`, `F_selcells(...)` | `gen/prims.c` |
| `𝕊` | A recursive call, e.g. `F_reverse(...)` | `gen/prims.c` |
| Trains and `∘ ○ ⊸ ⟜ ˜ ˙ ⊘ ◶ ⍟` | `mk_fn(D_fork, …)`, `mk_fn(D_after, …)`, … | `vm.c`, functions section |
| Blocks and modifiers used as values | `mk_fn(L_n, …)`, `mk_fn(M_…, …)` | `gen/prims.c` |
| Calling a function value | `call(f, w, x)` | `vm.c`, functions section |
| `!` | `p_assert(msg, cond)` | `vm.c`, arrays section |
| Destructuring, list literals, `?` | `need_list`, `list_get`, `mk_list`, `truth` | `vm.c`, arrays section |
| String literals | `S0`, `S1`, … static constants | `gen/prims.c` |

Every generated function has the signature `B F_name(B *e, B w, B x)`. `w`
is `NONE` for a monadic call, and `e` is the environment, which top-level
definitions don't use.

## Example 1: `⌽` (Reverse)

The general case of `Reverse` in `prims.bqn`, the fifth of its header cases:

```bqn
  𝕊 𝕩:
    "⌽: 𝕩 must have rank at least 1" ! 0 k.Lt RankOf 𝕩
    n ← k.Len 𝕩
    (k.Shape 𝕩) k.Reshape ((n k.Sub 1) k.Sub k.Range n) SelCells 𝕩 ;
```

becomes section `b4` of `F_reverse`:

```c
  b4:; {
  if (!is_none(w)) goto b5;               // header "𝕊 𝕩": monadic only, else try the next case
  B t28 = F_rankof(NULL, NONE, x);        // RankOf 𝕩   → another generated function
  B t29 = b_lt(N(0), t28);                // 0 k.Lt …   → basis
  B t30 = p_assert(S13, t29);             // "…" ! …    → S13 is the message string constant
  B t31 = b_len(NONE, x);                 // n ← k.Len 𝕩
  B v_n_8 = t31;
  B t32 = b_range(NONE, v_n_8);           // k.Range n   (right to left, so this comes first)
  B t33 = b_sub(v_n_8, N(1));             // n k.Sub 1
  B t34 = b_sub(t33, t32);                // (n-1) k.Sub range
  B t35 = F_selcells(NULL, t34, x);       // … SelCells 𝕩 → generated
  B t36 = b_shape(NONE, x);               // k.Shape 𝕩
  B t37 = b_reshape(t36, t35);            // k.Reshape
  return t37;
  }
```

- **Headers become guards.** Each `;`-separated case gets a label (`b0:`,
  `b1:`, …). A case whose header or `?` predicate fails jumps to the next
  label. The final label calls `vm_nomatch()`.
- **Every intermediate is named** (`t28`, `t29`, …), in BQN's right-to-left
  evaluation order. This ANF form is where the compiler will insert `dup` and
  `drop` once reference counting is on.
- **`𝕊` is a direct call.** The `runs` case, `k.MkRuns ⟨𝕊 v, 𝕊 c⟩`, becomes
  `F_reverse(NULL, NONE, v_v_4)` and `F_reverse(NULL, NONE, v_c_5)`.

## Example 2: a train and a modifier (AllNum)

```bqn
AllNum ← {1 k.Min k.FoldMin (1 k.Eq k.Type) k._each Els 𝕩}
```

```c
static B F_allnum(B *e, B w, B x) {
  b0:; {
  B t1 = F_els(NULL, NONE, x);                         // Els 𝕩
  B t2 = mk_fn(D_fork, 3, N(1), KV_eq, KV_type);       // (1 k.Eq k.Type), a 3-train
  B t3 = bm_each(t2, NONE, t1);                        // k._each
  B t4 = b_foldmin(NONE, t3);                          // k.FoldMin
  B t5 = b_min(N(1), t4);                              // 1 k.Min …
  return t5;
  }
  b1:; return vm_nomatch();
}
```

The train `(1 k.Eq k.Type)` isn't called directly. It is built as a function
object with `mk_fn(D_fork, …)`, whose parts are the number `1` and the basis
operations wrapped as function values (`KV_eq`, `KV_type`). `bm_each` calls
that object on each element through `call()`, which runs `D_fork` from the
functions section of `vm.c`.

## Summary

- The logic of each primitive lives in `prims.bqn` and compiles to `F_*`
  functions in `gen/prims.c`.
- `vm.c` provides what those functions call: `b_*` and `bm_*` from the basis
  section for the work, `mk_fn`, `call` and `D_*` from the functions section
  for trains and combinators, and small helpers from the arrays section.
- Milestone 1: the generated code does no reference counting yet, so there are
  no `dup`, `drop` or reuse operations in it.
