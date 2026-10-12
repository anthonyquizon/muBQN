# b.bqn: the kernel basis, defined in BQN.
#
# This is the specification of the basis, and the reference to test the C
# versions (b_* in vm.c) against. Dialect code (prims.bqn) receives this
# namespace as •args and may call nothing else that does real work.
#
# Every operation checks its contract and fails if it doesn't hold, so
# dialect code can't rely on more than the basis promises. Basis operations
# take lists (rank 1) unless noted, and "flat" means every element is a number.

Chk ← {𝕨 ! 𝕩 ⋄ @}
IsList ← {(0=•Type 𝕩) ∧ 1==𝕩}
IsFlat ← {IsList 𝕩 ? ∧´1=•Type¨𝕩 ; 0}
IsNat ← {(1=•Type 𝕩) ∧ (0≤𝕩) ∧ 𝕩=⌊𝕩}
NumOrFlat ← {(1=•Type 𝕩) ∨ IsFlat 𝕩}

# ---- queries. These read the header; any value is accepted.
IsArr ⇐ {0=•Type 𝕩}
Shape ⇐ ≢
Len ⇐ ≠                      # number of major cells; 1 for an atom
Count ⇐ {×´≢𝕩}               # number of elements
Type ⇐ •Type

# Flat 𝕩: 1 only if 𝕩 is a list of numbers. It is a hint for fast paths, not a
# fact to compute with: the C version answers 0 for a generic array that
# happens to hold only numbers. To keep dialect code honest, this version
# answers 0 at random a quarter of the time.
Flat ⇐ {(IsFlat 𝕩) ∧ 0<•rand.Range 4}

# Fill 𝕩: the fill element of a list.
Fill ⇐ {"b.Fill: 𝕩 must be a list" Chk IsList 𝕩 ⋄ ⊑1↑0↑𝕩}

# Same: identity of two values, used to compare function operands against
# known primitives. The compiler resolves it statically.
Same ⇐ ≡

# ---- construction
Reshape ⇐ {
  "b.Reshape: 𝕨 must be a list of naturals" Chk (IsList 𝕨) ∧ ∧´IsNat¨𝕨
  "b.Reshape: 𝕩 must be a list" Chk IsList 𝕩
  "b.Reshape: 𝕩 must have exactly ×´𝕨 elements" Chk (×´𝕨) = ≠𝕩
  𝕨⥊𝕩
}
Deshape ⇐ {"b.Deshape: 𝕩 must be an array" Chk IsArr 𝕩 ⋄ ⥊𝕩}
Range ⇐ {"b.Range: 𝕩 must be a natural number" Chk IsNat 𝕩 ⋄ ↕𝕩}
Cat ⇐ {   # list of lists → one list
  "b.Cat: 𝕩 must be a list of lists" Chk (IsList 𝕩) ∧ ∧´IsList¨𝕩
  ∾𝕩
}
Slice ⇐ {  # start‿len Slice 𝕩
  "b.Slice: 𝕨 must be start‿len" Chk (IsList 𝕨) ∧ (2=≠𝕨) ∧ ∧´IsNat¨𝕨
  "b.Slice: 𝕩 must be a list" Chk IsList 𝕩
  s‿l ← 𝕨
  "b.Slice: out of range" Chk (s+l) ≤ ≠𝕩
  l↑s↓𝕩
}
Pick ⇐ {   # i Pick 𝕩: one element; negative i counts from the end
  "b.Pick: 𝕩 must be a list" Chk IsList 𝕩
  "b.Pick: 𝕨 must be an index into 𝕩" Chk (1=•Type 𝕨) ∧ (𝕨=⌊𝕨) ∧ (𝕨≥-≠𝕩) ∧ 𝕨<≠𝕩
  𝕨⊑𝕩
}

# ---- arithmetic. Each argument is a number or a flat list; two lists must
# have the same length. Monadic: a number or a flat list.
_ar2 ← {
  "b: arithmetic on non-numbers" Chk (NumOrFlat 𝕨) ∧ NumOrFlat 𝕩
  "b: length mismatch" Chk (1=•Type 𝕨) ∨ (1=•Type 𝕩) ∨ 𝕨 =○≠ 𝕩
  𝕨 𝔽 𝕩
}
_ar1 ← {"b: arithmetic on non-numbers" Chk NumOrFlat 𝕩 ⋄ 𝔽 𝕩}
Add ⇐ + _ar2 ⋄ Sub ⇐ - _ar2 ⋄ Mul ⇐ × _ar2 ⋄ Div ⇐ ÷ _ar2 ⋄ Mod ⇐ | _ar2
Min ⇐ ⌊ _ar2 ⋄ Max ⇐ ⌈ _ar2
Eq ⇐ = _ar2 ⋄ Ne ⇐ ≠ _ar2 ⋄ Lt ⇐ < _ar2 ⋄ Le ⇐ ≤ _ar2 ⋄ Gt ⇐ > _ar2 ⋄ Ge ⇐ ≥ _ar2
Floor ⇐ ⌊ _ar1 ⋄ Abs ⇐ | _ar1

# ---- folds and scans over a flat list
_fl ← {"b: fold or scan needs a flat list" Chk IsFlat 𝕩 ⋄ 𝔽 𝕩}
FoldAdd ⇐ +´_fl ⋄ FoldMul ⇐ ×´_fl ⋄ FoldMax ⇐ ⌈´_fl ⋄ FoldMin ⇐ ⌊´_fl
ScanAdd ⇐ +`_fl ⋄ ScanMax ⇐ ⌈`_fl

# ---- selection
Gather ⇐ {  # 𝕨: flat list of indices (negatives count from the end)
  "b.Gather: 𝕨 must be a flat list" Chk IsFlat 𝕨
  "b.Gather: 𝕩 must be a list" Chk IsList 𝕩
  "b.Gather: index out of bounds" Chk ∧´(𝕨=⌊𝕨) ∧ (𝕨≥-≠𝕩) ∧ 𝕨<≠𝕩
  𝕨⊏𝕩
}
Scatter ⇐ {  # i‿v Scatter 𝕩: copy of 𝕩 with 𝕩[i[j]] = v[j]
  i‿v ← 𝕨
  "b.Scatter: 𝕩 must be a list" Chk IsList 𝕩
  "b.Scatter: i must be a flat list" Chk IsFlat i
  "b.Scatter: v must be a list as long as i" Chk (IsList v) ∧ i =○≠ v
  "b.Scatter: index out of bounds" Chk ∧´(i=⌊i) ∧ (i≥-≠𝕩) ∧ i<≠𝕩
  v⌾(i⊸⊏) 𝕩
}
Compress ⇐ {  # 𝕨: boolean list as long as 𝕩
  "b.Compress: 𝕨 must be a boolean list" Chk (IsFlat 𝕨) ∧ ∧´𝕨∊0‿1
  "b.Compress: 𝕩 must be a list as long as 𝕨" Chk (IsList 𝕩) ∧ 𝕨 =○≠ 𝕩
  𝕨/𝕩
}
Indices ⇐ {  # /𝕩 for a list of naturals
  "b.Indices: 𝕩 must be a list of naturals" Chk (IsFlat 𝕩) ∧ ∧´IsNat¨𝕩
  /𝕩
}

# ---- search and sort. Elements compare as BQN values (≡ and array ordering).
Grade ⇐ {"b.Grade: 𝕩 must be a list" Chk IsList 𝕩 ⋄ ⍋𝕩}
IndexOf ⇐ {   # for each element of 𝕩, its first index in 𝕨, or ≠𝕨
  "b.IndexOf: 𝕨 and 𝕩 must be lists" Chk (IsList 𝕨) ∧ IsList 𝕩
  𝕨⊐𝕩
}
Hist ⇐ {      # n Hist 𝕩: counts of each of ↕n in 𝕩
  "b.Hist: 𝕨 must be a natural number" Chk IsNat 𝕨
  "b.Hist: 𝕩 must be a list of naturals below 𝕨" Chk (IsFlat 𝕩) ∧ ∧´(IsNat¨𝕩) ∧ 𝕩<𝕨
  𝕨↑/⁼𝕩
}
Match ⇐ ≡     # any values

# ---- callbacks. 𝔽 is any function; these are the loops that call it.
_each ⇐ {
  𝔽 _𝕣 𝕩:
    "b._each: 𝕩 must be a list" Chk IsList 𝕩
    𝔽¨ 𝕩
  ;
  𝕨 𝔽 _𝕣 𝕩:
    "b._each: 𝕨 and 𝕩 must be lists of equal length" Chk (IsList 𝕨) ∧ (IsList 𝕩) ∧ 𝕨 =○≠ 𝕩
    𝕨 𝔽¨ 𝕩
}
_fold ⇐ {     # right to left; with 𝕨 as the initial value
  𝔽 _𝕣 𝕩:
    "b._fold: 𝕩 must be a non-empty list" Chk (IsList 𝕩) ∧ 0<≠𝕩
    𝔽´ 𝕩
  ;
  𝕨 𝔽 _𝕣 𝕩:
    "b._fold: 𝕩 must be a list" Chk IsList 𝕩
    𝕨 𝔽´ 𝕩
}
_scan ⇐ {     # left to right, monadic only
  "b._scan: 𝕩 must be a list" Chk IsList 𝕩
  𝔽` 𝕩
}

# ---- markers: opaque atoms that only compare by identity. Used by ⌾ to see
# where a structural function moves elements. Arithmetic on them fails.
Markers ⇐ {"b.Markers: 𝕩 must be a natural number" Chk IsNat 𝕩 ⋄ {𝕩⋄{⇐}}¨↕𝕩}
IsMarker ⇐ {6=•Type 𝕩}

# ---- encodings. A list may be stored compressed; dialect code can ask how
# and work on the parts directly. Like Flat, Enc is a hint: the name it
# returns is an encoding the list really has, and "plain" is always correct.
# Every other basis operation accepts any encoding.
#
#   "const"  v‿n      n copies of v
#   "range"  s‿d‿n    s+d×↕n, integers only
#   "runs"   v‿c      c/v; every count is at least 1, and neighbouring runs
#                     may hold equal values
#   "dict"   c‿d      c⊏d; d may hold repeats and entries no code uses
#
# Here lists are always plain, so Enc claims an encoding at random from those
# the list could have, and Parts derives the parts with the freedom each
# encoding allows (shuffled and padded dictionaries, split runs, any step for
# a one-element range). Stats counts the parts taken and lists built.
IsInt ← {1=•Type 𝕩 ? (𝕩=⌊𝕩) ∧ 9007199254740992>|𝕩 ; 0}
encs ← "const"‿"range"‿"runs"‿"dict"
taken ← 0¨ ↕2×≠encs
Count1 ← {taken +↩ 𝕩 = ↕≠taken ⋄ @}
Stats ⇐ {𝕤 ⋄ ⟨encs∾("Mk"∾⊢)¨encs, taken⟩}

Can ← {   # encodings list 𝕩 could have
  ¬IsList 𝕩 ? 0¨encs ;
  c ← {0<≠𝕩 ? ∧´(⊑𝕩)⊸≡¨𝕩 ; 0} 𝕩
  Ar ← {d ← (1↓𝕩)-¯1↓𝕩 ⋄ ∧´d=⊑d∾0}
  r ← (0<≠𝕩) ∧ {∧´IsInt¨𝕩 ? Ar 𝕩 ; 0} 𝕩
  c‿r‿1‿1
}
Enc ⇐ {(•rand.Range ≠o) ⊑ o ← (<"plain") ∾ (Can 𝕩)/encs}
Parts ⇐ {
  "b.Parts: unknown encoding" Chk ⊑(<𝕨) ∊ encs
  e ← ⊑encs ⊐ <𝕨
  ("b.Parts: 𝕩 is not "∾𝕨) Chk e ⊑ Can 𝕩
  Count1 e
  e ◶ ⟨
    {⟨⊑𝕩, ≠𝕩⟩}
    {⟨⊑𝕩, (1<≠𝕩) ◶ ⟨{𝕤⋄¯2+•rand.Range 5}, {(1⊑𝕩)-⊑𝕩}⟩ 𝕩, ≠𝕩⟩}
    {   # runs, with some runs split in two
      0=≠𝕩 ? ⟨⟨⟩, ⟨⟩⟩ ;
      s ← / 1 ∾ ¬(1↓𝕩) ≡¨ ¯1↓𝕩
      c ← (1↓s∾≠𝕩) - s
      sp ← (c>1) ∧ 0=•rand.Range¨ 3¨c       # runs to split
      a ← 1 + •rand.Range¨ 1⌈c-1             # length of the first part
      Split ← {𝕊 s‿a‿c: s ? ⟨a, c-a⟩ ; 𝕊 s‿a‿c: ⟨c⟩}
      ⟨(1+sp) / s ⊏ 𝕩, ∾ Split¨ <˘⍉> sp‿a‿c⟩
    }
    {   # dict: unique values, some repeated, some unused, in random order
      u ← ⍷𝕩
      extra ← ((•rand.Range 1+≠u) •rand.Subset ≠u) ⊏ u
      junk ← (∧´ 1=•Type¨ 𝕩) ◶ ⟨⟨⟩, {𝕤 ⋄ 1000 + •rand.Range¨ 3⥊100}⟩ @
      d ← u ∾ extra ∾ junk
      d ↩ (•rand.Deal ≠d) ⊏ d
      ⟨d ⊐ 𝕩, d⟩
    }
  ⟩ 𝕩
}

MkConst ⇐ {
  v‿n ← 𝕩
  "b.MkConst: n must be a natural number" Chk IsNat n
  Count1 4 ⋄ n ⥊ <v
}
MkRange ⇐ {
  s‿d‿n ← 𝕩
  "b.MkRange: s and d must be integers" Chk (IsInt s) ∧ IsInt d
  "b.MkRange: n must be a natural number" Chk IsNat n
  "b.MkRange: elements must stay integers" Chk IsInt s + d × 0⌈n-1
  Count1 5 ⋄ s + d × ↕n
}
MkRuns ⇐ {
  v‿c ← 𝕩
  "b.MkRuns: v and c must be lists of equal length" Chk (IsList v) ∧ (IsList c) ∧ v =○≠ c
  "b.MkRuns: counts must be at least 1" Chk ∧´ (IsNat¨c) ∧ c≥1
  Count1 6 ⋄ c / v
}
MkDict ⇐ {
  c‿d ← 𝕩
  "b.MkDict: d must be a list" Chk IsList d
  "b.MkDict: codes must index d" Chk (IsFlat c) ∧ ∧´ (IsNat¨c) ∧ c<≠d
  Count1 7 ⋄ c ⊏ d
}

# Sorted 𝕩: 1 only if 𝕩 is a list in ascending order. A hint, like Flat.
Sorted ⇐ {(IsList 𝕩) ∧ (𝕩 ≡ ∧𝕩) ∧ 0<•rand.Range 4}
