# Learning path: rebuilding by hand

`src/vm.c`, `src/gen/` and `src/singeli/` were sketched with LLM help. This is a
plan for rebuilding the same ideas by hand in `src/vm.aq.c`, so that every
line is understood.

Rules:

- **Attempt, then compare.** The LLM-written code is the answer key: read it
  after an attempt, not before.
- **CBQN is the oracle.** `test/hand.bqn` runs random cases through
  `vm.aq.c` and through CBQN. If they disagree, either you have a bug or
  there's something to learn.
- **Build one thin slice through every layer.** Get one function working
  through every layer before adding a second.
- **Keep notes.** After each stage, write a line or two below on what was
  surprising.

## The harness

```
bqn test/hand.bqn [cases per test] [seed] [test name...]
bqn test/hand.bqn 200 1 "𝕨+𝕩" "+´𝕩"      # the default tests
```

Test names come from the `tests` list in `test/gen.bqn`. The harness builds
`test/hand_main.c` (which includes `src/vm.aq.c`) with AddressSanitizer, so a
use-after-free or double free stops the run and names the case. It also
reports any successful case that left more objects alive than it started
with.

`vm.aq.c` has to provide a small API, listed at the top of
`test/hand_main.c`:

- value accessors
- `t_mkarr`/`t_get`/`t_rank`/`t_shape`/`t_len`
- `v_drop`
- `t_call(src, w, x)`, which dispatches on the primitive's spelling
- `t_live`
- the `err_jmp`/`err_msg` pair

Stub out the parts you haven't written yet, for example `t_mkarr` calling
`vm_error`. Guard your own `main` with `#ifndef HAND_TEST`.

## Stages

### 1. Values

Write NaN-boxing: `mk_num`/`num`, `mk_chr`/`chr`, `mk_ptr`/`ptr`, and NaN
canonicalisation.

- Done when: `0`, `¯0`, `∞`, NaN and characters round-trip, and atom-only
  cases of `𝕨+𝕩` pass.
- Read afterwards: CBQN's tag table, `_ref/cbqn/src/core/h.h:172`. Why are
  characters at `7FF1` and pointers at `FFF*`? What does `isF64`'s
  subtraction trick (`h.h:445`) buy?

### 2. Arrays and reference counting

Write the `H` header, allocation, `dup`/`drop`, and f64 lists. Implement
`t_live`.

- Done when: no leaks are reported, and ASan stays quiet.

### 3. One function: dyadic `+`

Cover atom+atom, atom+list and list+list, a length error, and arguments of
different rank (leading-axis agreement). Reuse an argument's buffer when its
refcount is 1. That reuse is the core idea of Perceus.

- Done when: `𝕨+𝕩` passes, and a counter shows buffers being reused.
  Nested arrays (pervasion) are a stretch goal.
- Read afterwards: `_ref/cbqn/src/builtins/arithd.c`. Most of it is type
  dispatch.

### 4. One modifier: `´` (fold)

This stage covers:

- functions as values (`´` takes a function operand)
- identity values: `+´⟨⟩` is `0`, `⌈´⟨⟩` is `¯∞`
- a fast path when the operand is `+` or `⌈`, and a general path that calls
  any function

Question to answer: `´` is a right fold, and float addition isn't
associative. Does CBQN's `+´` match a naive right-to-left loop bit for bit?
Why, or why not? What does that mean for differential tests?

- Done when: `+´𝕩`, `⌈´𝕩` and `-´𝕩` pass, and the general path works for
  `∾´𝕩`.

### 5. Singeli on its own

Do this outside the VM. Install the Singeli compiler, write `add.singeli`
(f64 add with NEON vectors), generate C, and call it from a tiny test
program. Then write a fold with several accumulators.

- Done when: it beats your scalar loop and is correct when `dst == src`.
- Read afterwards: CBQN's `base.singeli`, `neon.singeli`, and the f64 parts
  of `fold.singeli`.

### 6. Put them together

Swap your kernels into `+` and `+´`. Then build CBQN's `fold.singeli` through
`src/singeli/muDefs.singeli` and `si_prelude.h`. At that point every line of
the shim should make sense.

### Next

- `/` with a boolean left argument. This forces bit arrays (milestone 2 in
  `design.md`).
- `⊏` with i32 indices.
- The bytecode VM that runs `src/c.bqn`'s output. This is a separate track;
  stages 1 to 5 don't need it.

## Notes

<!-- a line or two per stage -->
