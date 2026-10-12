# memBQN: a Perceus-style BQN subset

Status: design sketch. Nothing implemented yet.

## Goal

Compile a subset of BQN to an IR with **explicit memory instructions**
(`dup`, `drop`, `drop_reuse`, `alloc_at`) inserted by the compiler using the
Perceus approach, executed by a minimal C runtime (`src/vm.c`).

Perceus (Koka) gives precise reference counting: the compiler inserts `dup` and
`drop` so each value is freed at its last use, and pairs dead values with new
allocations of the same size so their memory is reused. It needs two things:

1. No reference cycles, so reference counting is complete.
2. Ownership that the compiler can see.

## Why BQN fits

- **Values are immutable.** Arrays cannot form cycles, so no cycle collector is
  needed.
- **Primitives are where reuse pays off.** Koka reuses memory by matching
  constructors. In BQN the wins come from primitives (`x+1`, `⌽x`, `F¨x`,
  `x∾y`) working in place when they receive the only reference. The compiler's
  main job is to hand primitives **owned** arguments at last use. The runtime
  checks `rc==1` and writes into the existing buffer.
- **Atoms cost nothing.** With tagged or NaN-boxed values, `dup`/`drop` on a
  number is a tag check. Drop specialization removes even that when the
  compiler knows a value is an atom.
- **Roles are syntactic.** Whether a name is a subject, function or modifier is
  known at parse time, which keeps the IR simple.

## Subset restrictions

Cycles and hidden control flow come from a few features:

| Feature | Problem | Subset rule |
|---|---|---|
| `↩` on captured variables | Closures over mutable environments create cycles | Allow `↩` only on locals no closure captures (or box them) |
| Named local functions in a block | A function stored in the environment it captures is a cycle | Use **flat closures** that capture values, not environment frames. Self-recursion goes through `𝕊`; top-level definitions are static |
| Mutually recursive local functions | letrec cycle | Disallow, or lift them to top level |
| `⎊` (catch) | Non-local exits need drops on the unwind path | Omit in v1 |
| `•`-system values | Large surface | A small whitelist only |

Kept: trains, 1- and 2-modifiers, blocks with `𝕨 𝕩 𝕗 𝕘 𝕊`, standard
primitives, and namespaces as static imports only (below).

## Namespaces: static imports only

In full BQN a namespace *is* a block's environment. Functions defined in that
block close over the same environment, so the environment points to the
function and the function points back to it: a cycle. `↩` inside the block also
makes the namespace a mutable view. The subset avoids all of this by supporting
only **static imports**.

### Rules

- `•Import` takes a **string literal** path. The compiler loads and compiles
  the imported file itself.
- An import may only be bound to a name or destructured:
  `m ← •Import "x.bqn"` or `⟨F, G⟩ ← •Import "x.bqn"`.
- A module name can only be used in field access (`m.F`). It cannot be passed,
  returned, stored in arrays or compared. Modules are **compile-time only**, so
  there is no runtime namespace object.
- Field access resolves at **compile time** to a static slot or a direct call.
- Module top-level bindings are **immutable** after initialization (no `↩`
  on them, from inside or outside the module).
- Each module is initialized once, in dependency order. Import cycles are a
  compile error.
- Blocks that export with `⇐` are only allowed at module top level. A block
  that would produce a namespace at runtime is a compile error.

### Why this has no cycles

- Module-level values live in **static slots**, which are roots rather than
  heap objects. Like Koka and Lean static data, they are never reference
  counted.
- Functions in a module refer to module-level names through those slots and do
  not capture an environment. Mutual recursion between module-level functions
  goes through the slots too, so it creates no cycle.
- Calls are resolved statically, which also allows borrow inference and
  specialization across modules.

### Deferred

Runtime namespaces as reference-counted records (`{a⇐𝕩 ⋄ b⇐2×𝕩}` inside a
function) would also be acyclic under flat closures, apart from mutually
recursive exported functions. They are out of scope until there is a need.

## Pipeline

```
subset source
  → parse + scope resolution
  → ANF-style IR: every intermediate named, evaluation order explicit (right to left)
  → liveness analysis
  → Perceus: insert dup/drop, infer borrowed parameters (as in Lean/Koka)
  → reuse pairing (drop + same-size alloc → reuse token), drop specialization
  → emit, by source kind:
      user code          → bytecode / IR → vm.c executes, including the explicit memory operations
      primitive dialect  → C, compiled ahead of time and linked with vm.c and the kernels
```

## Example output

`{𝕩 + ⌽𝕩}`: BQN evaluates `⌽𝕩` first, so the left `𝕩` is the last use.

```
fn(x):                 ; x is owned by the callee
  dup  x               ; one ref for ⌽, one kept for +
  t  = rev  x          ; consumes a ref; rc(x)=2 so it allocates
  r  = add  x, t       ; consumes both; rc==1 for both now, so it writes into one in place
  ret r
```

Reuse tokens, which matter for strands and list literals:

```
  tok = drop_reuse a          ; a is dead; if rc==1, keep its block as a token
  r   = alloc_at tok, [2]     ; reuse the block if it fits, otherwise malloc
```

## Runtime contract (`vm.c`)

- **Value representation:** tagged value; the heap header holds `rc`, type,
  rank, shape and capacity.
- **Primitive ownership:** each primitive has a fixed convention. For example,
  `⊑` and `≠` borrow, while arithmetic, `⌽` and `∾` consume their arguments and
  may reuse them.
- **Calling convention:** user functions own their arguments by default, and
  borrow inference relaxes that per parameter.
- **Higher-order primitives:** `¨ ⌜ ´` call back into compiled code under the
  same convention. `F¨x` with a unique `x` can update cells in place.
- **Memory instructions:** `dup`, `drop`, `drop_reuse`, `alloc_at`.
- **Static slots:** module-level values and constants live in static storage.
  A flag on static heap values makes `dup`/`drop` skip them.
- **Debug mode:** asserts every reference count returns to zero at exit. This is
  the main check that the compiler's analysis is correct.

### One hand-written C file

All hand-written C lives in `src/vm.c`. Generated C (primitives, Singeli
kernels) goes in `src/gen/` and is `#include`d into `vm.c` at a fixed point, so
the whole program is one compilation unit:

```
runtime      values, rc, reuse tokens
kernels      scalar fallbacks with the (dst, src, n) shape
basis        kernels as value-level operations with an ownership convention
generated    #include "gen/kernels.c", #include "gen/prims.c"
interpreter
main         -DPRIM_TEST swaps in the primitive test harness
```

- There are no headers. Generated code sees the runtime's `static` definitions
  directly, and the C compiler can inline across all of it without link-time
  optimization.
- Anything generated code calls must come before the `#include`s, or be
  forward-declared there (like `vm_call`).
- The build is `cc -O2 src/vm.c`, and the hand-written C budget is that file's
  line count.

## Performance strategy

Most of CBQN's `builtins/` is not fast kernels. It is the surrounding work:
every primitive handled for every element type and rank, plus fills, errors and
fallbacks. The plan is to keep that surrounding work small and write only a few
fast kernels.

### Primitives in BQN over a kernel basis

Primitives are written in BQN and stay there. CBQN started with primitives in
self-hosted BQN (`r1.bqn`) and replaced them with hand-written C; today only a
few slow paths (`⚇` with non-zero depth, `⁼` on a non-function, some `⌾`)
still call into `r1.bqn`. We keep the BQN source and generate that C from it
instead. Native code is a small **kernel basis**, and the primitives are built
from it.

Array-at-a-time BQN pays overhead per call, not per element. A primitive written
as a fixed number of whole-array operations, each of which is a native kernel,
runs close to native speed on large arrays. For example:

- `⌽𝕩` → gather with a descending range
- `𝕨/𝕩` with boolean `𝕨` → compress. General `/` → indices, then gather.
- `∊`, `⊐`, `⊒`, `⍷` and `⊔` → grade, sort, hash, scans, gather and scatter
- `↑`, `↓`, `«`, `»`, `∾` and `≍` → slice, copy and reshape
- `⎉`, `⌜` and higher ranks → reshape plus the list kernels

A first guess at the basis (about 20–30 kernels):

- elementwise arithmetic and comparisons (to bits)
- range (`↕`)
- reshape and copy
- gather (`⊏`) and scatter
- compress (boolean `/`)
- indices (`/` on counts)
- `+ ⌈ ⌊ ∨ ∧` folds and scans
- grade, sort and hashing
- join and slice
- type and fill queries

A primitive moves into native code only when it cannot be written as a fixed
number of kernel calls, as with sorting, hashing or string search.

On small arrays the cost is dispatch, not the kernels. Primitives are therefore
compiled ahead of time to C rather than interpreted (see
[Primitive dialect](#primitive-dialect)).

### Few element types

Code size grows roughly as primitives × element types × type pairs. Native
types:

| Type | Why |
|---|---|
| bit | Fast `=`, `<`, `/`, `∧`; leaving it out costs the most |
| i32 | One integer width; overflow promotes to f64 |
| f64 | |
| u32 char | Possibly later |
| generic | Boxed elements |

There is no i8 or i16, so no squeeze or widen logic. Fewer types also helps
reuse: when a result has the same type as its input, it can be written into the
input's buffer, and with fewer types this happens more often.

### Compressed lists

Inspired by l (lv1.sh), which runs primitives directly on compressed vectors.
Its site names no specific encodings, so these come from the usual
column-store set. A list may be stored in one of these encodings, each made
of plain lists and numbers:

| Encoding | Parts | Meaning |
|---|---|---|
| const | `v‿n` | `n` copies of `v` |
| range | `s‿d‿n` | `s+d×↕n`, integers only |
| runs | `v‿c` | `c/v`; counts are at least 1, and neighbouring runs may be equal |
| dict | `c‿d` | `c⊏d`; `d` may have repeats and unused entries |

There is also a sorted flag, like kdb+'s `s#`.

- **Kernels don't change.** They run on plain lists, and an encoding's parts
  are plain lists. Every basis operation accepts any encoding and decodes what
  it doesn't handle, so correctness never depends on a fast path.
- **The compressed-data algorithms are dialect code.** A primitive asks
  `b.Enc` how a list is stored, takes `b.Parts`, and builds results with
  `b.MkConst`, `b.MkRange`, `b.MkRuns` and `b.MkDict`. For example,
  `𝕨∊𝕩` on a dict searches only the dictionary: `b.MkDict ⟨c, d∊𝕩⟩`.
- **Encodings mostly come from primitives, not from scanning data.** `↕n`
  is a range, `n⥊x` is a const, and `/` with long runs is runs. A
  dictionary is kept through `⊏`, `/`, `⌽` and arithmetic with an atom.
  Scanning data to choose an encoding belongs at I/O boundaries.
- **Exactness.** Shortcuts that change floating-point rounding are not
  allowed. `+´` on a const takes `n×v` only for integers, and range
  arithmetic is limited to integers and to `+ - ×`, the operations that are
  affine in each argument.
- **Runtime cost.** An encoding tag in the header, parts as reference-counted
  children (so arrays can share one dictionary), and one decode function per
  encoding.
- **Not chunked.** Column stores split a list into chunks, each with its own
  encoding, so that one irregular value only spoils its chunk. That matters
  when encodings are chosen by scanning data. Here they come from
  primitives and cover the whole list, and `↑`/`↓` work on every encoding
  without chunks. Chunks would cost a lot: `𝕨+𝕩` on two chunked lists must
  line up their boundaries, scans and `⍷ ⊐ ∊ ⍋` cross boundaries, float folds
  must carry the accumulator from chunk to chunk to keep rounding exact, and
  small arrays pay dispatch per chunk. If a benchmark shows `∾` decoding
  encoded lists, or large data gets read in by scanning, chunks get added as
  one more encoding, cat `⟨l₀, l₁, …⟩` meaning `∾` of the parts, each of
  which may be encoded. Basis operations decode it like any other encoding,
  `Parts` tests it by splitting lists at random points, and primitives
  handle it one at a time: elementwise functions map over the parts, `∾`
  builds a cat, and folds pass the running result as `𝕨`.

### Lists only in the basis

Kernels and basis operations take lists only. Primitives handle every rank in
the dialect, and so in the generated C, by treating an array as a shape plus
its list of elements: higher ranks, cells and `⎉` become reshapes, cell
index computations and gathers over the list operations. There is no
interpreted fallback. Unlike CBQN, there is no dedicated C for higher-rank
cases (row copies, transpose kernels, row hashing); those get added as
kernels only where a benchmark shows a gap.

### Singeli as a kernel library

- Kernels are plain C functions such as `(dst, a, b, n)` that know nothing about
  BQN arrays. The C generated from the primitive dialect checks types and `rc`,
  then calls a kernel.
- We vendor CBQN's `src/singeli/src/` (under MPL2) instead of writing our own
  kernels. The kernels take raw pointers. Their only CBQN dependencies come
  through `cbqnDefs.singeli`, and `src/singeli/muDefs.singeli` replaces it,
  keeping the same names. The C side of those names is
  `src/singeli/si_prelude.h`. CBQN's C dispatch (`src/builtins/*.c`) is not
  vendored. It is rewritten against our `H` header in the primitive dialect.
- Most kernels need narrow element types (bit, i8, i16, i32). Only the f64
  paths apply until milestone 2 adds those types.
- One target architecture (NEON on Apple Silicon) plus a scalar fallback.
- Elementwise kernels must be correct when `dst == src`, so they work with
  `drop_reuse`.
- Kernel order:
  1. elementwise arithmetic, and comparison producing bits
  2. `+´` and `⌈´` folds, `` +` `` scan
  3. `/` with a boolean left argument
  4. `⊏` with i32 indices
  5. `⍋` and `∊`, later

### Benchmark-driven

A fixed set of 5–10 benchmark programs decides what gets native code. On small
arrays, time goes mostly to per-call interpreter overhead, not SIMD. There, the
compiled IR, with roles and ownership known statically, should matter more than
kernels.

### Testing against CBQN

- Differential testing: run subset programs on CBQN and on this VM, and compare
  the results. Each primitive also gets random-input fuzzing.
- Pull applicable cases from `BQN/test/cases/`.
- Together with the debug-mode rc balance check, this catches both wrong
  results and refcount bugs.

### Performance milestones

These start after milestone 1 below and run alongside the rest:

1. Tagged values, f64-only arrays, and scalar C versions of the kernel basis.
   All primitives are compiled from the primitive dialect.
2. Add bit and i32 types, with scalar C kernels that reuse unique buffers.
3. Replace the hot scalar kernels with Singeli versions for one architecture.
4. Measure against CBQN and add kernels only where there is a gap.

## Primitive dialect

Primitives are written in a restricted BQN dialect and compiled **ahead of
time to C** by the same compiler, as a second backend of the same Perceus IR.
The VM never interprets primitive code. Primitives get dup/drop, reuse and
borrow inference like any other code, and the generated C calls kernels
directly, so the C compiler can inline across them.

The dialect needs less than user code, but everything in it must be statically
resolvable. Otherwise the generated C would just be slow boxed calls without
the dispatch loop.

### Allowed

- Blocks with `𝕨 𝕩 𝕊`, monadic and dyadic cases (`;` or `⊘`), and predicates
  `?` for case splits on type and rank.
- 1- and 2-modifiers with `𝕗 𝕘 𝔽 𝔾`, since `¨ ⌜ ´ ⎉ ⍟ ⌾` are primitives
  themselves. The operand is an opaque callable (see below).
- Local definitions, trains, and flat closures over immutable values.
- `!` for errors.
- `↩` only on locals that no closure captures.
- Basis operations `b.Name` (below).

### Excluded

- Namespaces and `•Import`, apart from the basis namespace `b`.
- `•` system values, apart from `•args` to bind `b`.
- Functions stored in arrays, or other first-class functions used as data.
- `⎊`.

### Glyphs and the basis

- A primitive glyph in dialect source always means the dialect's **own
  definition** of that primitive, never a native one. `n-1` calls the dialect's
  `-`.
- Each glyph has a fixed name (`⌽` is `Reverse`, `¨` is `_each`), and a dialect
  file defines a glyph by exporting that name: `Reverse ⇐ {…}`. One definition
  covers both valences.
- The **basis** is a namespace `b`, bound at the top of the file with
  `b ← •args`. Basis operations are called by name, e.g. `b.Gather`. They match
  the `b_*` functions in `vm.c`: value-level, with lists only, and with a fixed
  ownership convention.
- A few glyphs are **pass-through**: the compiler handles them directly, and they
  keep their BQN meaning. They are the combinators `∘ ○ ⊸ ⟜ ˜ ˙ ⊘ ◶ ⊢ ⊣`, plus
  `!` and `⍟`.

`src/b.bqn` defines the basis in BQN, checking each operation's contract, for
example that arguments are lists. It is both the specification of the basis and
a reference to test the C kernels against.

### Dependency rule

A definition may use only glyphs whose definitions come **earlier** in the file,
plus basis operations and pass-through glyphs. Using its own glyph is also
rejected, since recursion goes through `𝕊`.

```bqn
Reverse ⇐ {n←b.Len 𝕩 ⋄ (n-1+↕n)⊏𝕩}   # needs - + ↕ ⊏ defined above; using ⌽ is rejected
```

`src/dialect.bqn` checks the rule. It rewrites each glyph to its name, so the
checked source runs on CBQN with `src/b.bqn` as the basis. This is the
front end the compiler will later share.

### Specialization

- A primitive is specialized only on **element type at entry**. A predicate on
  `b.Type` splits it into one C body per type, with at most one per native type.
- Dyadic primitives promote both arguments to a common type rather than
  generating every type pair.
- A modifier is monomorphized only for **primitive** operands: `+´` gets its own
  C function. With a user-defined operand it takes a generic path.
- Each primitive keeps a generic boxed fallback. Further variants are added only
  where a benchmark shows a gain.

### Boundary with the VM

- Each primitive compiles to a C function with a fixed signature, and the VM
  calls it like any other primitive under the ownership convention in
  [Runtime contract](#runtime-contract-vmc).
- A user-defined operand, such as `F` in `F¨x`, is called back through one entry
  point, `vm_call(f, w, x)`, with the same ownership convention.
- Primitive code needs no other VM feature.

### Build

- The compiler is written in BQN and runs on CBQN. It emits C for the
  primitives.
- The generated C is **checked in**, so building `vm.c` needs only a C
  compiler. CBQN is needed only to work on the compiler.
- [codegen.md](codegen.md) walks through the generated C for an example
  primitive and shows which parts of `vm.c` it calls.
- Test primitives three ways: compiled to C, run on CBQN, and fuzzed on random
  inputs.

## Milestones

Ordered by risk: the least proven parts come first.

0. **Dialect spike on CBQN.** No compiler: write about ten primitives in the
   dialect over the basis, including the hard ones (`⊐ ⊔ ∊ ⍷ ⎉ ⌾`), and check
   them against CBQN's built-ins on random inputs. This tests whether the basis
   and the dependency rule can express BQN.
   **Result (first round).** `src/prims.bqn` (376 lines) defines 43 glyphs
   over 48 basis operations in `src/b.bqn`. `test/prims.bqn` runs 90 tests
   (primitives, valences and derived functions) on random arguments against
   CBQN. At 500 cases each there are 0 mismatches. The gaps are the
   unsupported features listed at the top of `prims.bqn`, plus the two below
   that need design work. Findings:
   - **Fixed number of kernel calls:** this holds for everything on lists and
     flat arrays. It fails for `⍷` (one call per element of 𝕨), for `⊐ ∊ ⍋`
     on rank ≥ 2 (one call per cell, since cells are compared as boxed
     arrays) and for `↕` on a list. Candidate native kernels: list search, and
     hashing and comparison of rows.
   - **Fills** come from `b.Fill`, which relies on CBQN tracking fills. The C
     runtime has to store or derive a fill for generic arrays. `≡` ignores
     fills, so the tests do not check them yet.
   - **`⎉` with an empty frame** applies 𝔽 to a cell of fills to find the
     result shape. CBQN catches an error there and carries on, which the
     dialect can't do without `⎊`. Either add a basis `b._try` or accept the
     gap.
   - **Structural `⌾`** works by applying 𝔾 to an array of opaque markers
     (`b.Markers`). The runtime needs a marker type, and computational under
     is a separate piece of work.
   - **Fast paths don't change results.** `b.Flat` returns 0 at random a
     quarter of the time, and the tests still pass. Operand identity
     (`𝕗 b.Same plus`) selects fast paths and fold identities; the compiler
     must resolve it statically.
   - **The dialect needs two checks.** BQN names ignore case and underscores,
     so a local `els` silently shadowed the helper `Els`; the checker should
     reject locals that match a top-level name. Also, `;` bodies don't share
     scope, so case splits recompute their setup (see `_rank_`); the compiler
     should share that work, or the dialect needs a statement-level
     conditional.
   - `b.Compress` went unused: indices plus gather cover boolean `/`.
     Compress becomes an optimization kernel rather than a required one.
0b. **Encodings spike on CBQN.** Done. `src/b.bqn` stores every list plain, so
   `b.Enc` claims a random encoding from those the list could have, and
   `b.Parts` uses each encoding's full freedom: shuffled dictionaries with
   repeats and unused entries, split runs, and any step for a one-element
   range. Encoded paths cover `+ - ×` and the other elementwise operations
   with an atom, monadic arithmetic, `+´ ⌈´`, `⊏` (including a range of
   indices as a slice), `⌽`, `/`, `⊐ ∊`, `⍋`, `∧`, and making `↕` and `⥊`.
   At 1000 cases per test there are 0 mismatches, and the encoded paths ran
   over 100,000 times. Speed can only be measured in C.
1. **Compiler sketch.** Parse the dialect, convert to ANF, and emit C with no
   reference counting. Cover a monomorphized modifier (`+´`), a type split and
   a callback (`F¨` through `vm_call`). Link into `vm.c` and check against CBQN.
   **Progress.** `src/c.bqn` parses the dialect, after `dialect.bqn` has
   rewritten the glyphs, and emits C for all of `src/prims.bqn` (about 3,400
   lines). The parser is checked by printing the AST back as fully
   parenthesized BQN and running the dialect tests on that. `src/vm.c` has the
   runtime and the C basis, and `test/emit.bqn` runs the shared tests
   (`test/gen.bqn`) on the compiled C. Result: 0 mismatches at 500 cases per
   test. Calls to top-level definitions, basis operations, `𝕊` and modifiers
   applied on the spot are direct C calls; local blocks are flat closures.
   Still to do: monomorphization (fold `b.Same`, and so `+´`, when the operand
   is known, and drop dead bodies), and a type split resolved at compile time.
   Dialect rules this turned up:
   - A `𝕨` header (`𝕨 𝕊 𝕩:`) is dyadic only. In BQN it also matches a monadic
     call, which prims.bqn never relies on.
   - Each `;` body has its own scope, as in BQN, so names set before a
     predicate are not visible in later bodies.
2. **Perceus** on that IR: rc balance, plus counts of in-place updates and
   allocations with and without the pass.
3. **Small-array benchmark:** compiled primitives against CBQN. This decides
   whether the approach is worth it.
4. **VM for user code:**
   1. Straight-line subset: tacit and explicit expressions, no blocks.
   2. Blocks and flat closures; `𝕊` recursion.
   3. Borrow inference.
   4. Reuse tokens and drop specialization.
   5. Static imports via `•Import`.

## Future: sparse arrays

Graph algorithms written in array notation work over sparse matrices: the
GraphBLAS approach of linear algebra over semirings such as min-plus and
or-and. Sparse arrays would be another encoding, but they differ from the
list encodings in two ways:

- **Decoding is not a safe fallback.** Decoding a sparse adjacency matrix for
  a million nodes means 10¹² cells. Above a size limit, a basis operation that
  can't handle the encoding must fail rather than densify silently.
- **Matrix product is an idiom, not a primitive.** BQN writes it as
  `+˝∘×⎉1‿∞`, so the compiler has to recognize the pattern to call a sparse
  kernel. This is the same static operand matching as monomorphizing `+´`.

Design points:

- **A background value instead of zero.** An elementwise operation with an
  atom then always stays sparse: `x+1` changes only the background.
- **Exactness.** Min-plus, or-and and integer arithmetic are exact in any
  order. Floating-point sums are not, so they need the same rule as `+´` on
  encodings.
- **Switching representations.** The producer chooses, since it already knows
  how many entries are non-background (as `/` does for runs). Go sparse below
  about 10% density and dense above about 25–30%, with the gap preventing
  flip-flopping. The exact thresholds come from benchmarks.
- **Cheaper first step.** Much graph code in BQN uses adjacency lists
  (`∾ frontier⊏adj`). Storing a list of lists as one flat list plus offsets
  gives much of the benefit, and also speeds up `⊔`.

When: after milestones 1–3, once encodings exist in C. Spike it on CBQN first,
as in 0b, with BFS, shortest paths and PageRank written in plain BQN as the
test programs.

## Open questions

- Code-size budget: a line cap on `src/vm.c`, and a
  separate cap on generated C or binary size, checked in CI.
- Later: write the VM itself in a lower-level "systems BQN" dialect, compiled to
  C and bootstrapped through CBQN (as PreScheme and Squeak's Slang do). Out of
  scope for now. `vm.c` stays hand-written and minimal.
- Bytecode format: reuse the shape of standard BQN bytecode, or a register IR
  better suited to explicit memory operations.
