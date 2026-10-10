# k.bqn: the kernel basis, defined in BQN.
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
Fill ⇐ {"k.Fill: 𝕩 must be a list" Chk IsList 𝕩 ⋄ ⊑1↑0↑𝕩}

# Same: identity of two values, used to compare function operands against
# known primitives. The compiler resolves it statically.
Same ⇐ ≡

# ---- construction
Reshape ⇐ {
  "k.Reshape: 𝕨 must be a list of naturals" Chk (IsList 𝕨) ∧ ∧´IsNat¨𝕨
  "k.Reshape: 𝕩 must be a list" Chk IsList 𝕩
  "k.Reshape: 𝕩 must have exactly ×´𝕨 elements" Chk (×´𝕨) = ≠𝕩
  𝕨⥊𝕩
}
Deshape ⇐ {"k.Deshape: 𝕩 must be an array" Chk IsArr 𝕩 ⋄ ⥊𝕩}
Range ⇐ {"k.Range: 𝕩 must be a natural number" Chk IsNat 𝕩 ⋄ ↕𝕩}
Cat ⇐ {   # list of lists → one list
  "k.Cat: 𝕩 must be a list of lists" Chk (IsList 𝕩) ∧ ∧´IsList¨𝕩
  ∾𝕩
}
Slice ⇐ {  # start‿len Slice 𝕩
  "k.Slice: 𝕨 must be start‿len" Chk (IsList 𝕨) ∧ (2=≠𝕨) ∧ ∧´IsNat¨𝕨
  "k.Slice: 𝕩 must be a list" Chk IsList 𝕩
  s‿l ← 𝕨
  "k.Slice: out of range" Chk (s+l) ≤ ≠𝕩
  l↑s↓𝕩
}
Pick ⇐ {   # i Pick 𝕩: one element; negative i counts from the end
  "k.Pick: 𝕩 must be a list" Chk IsList 𝕩
  "k.Pick: 𝕨 must be an index into 𝕩" Chk (1=•Type 𝕨) ∧ (𝕨=⌊𝕨) ∧ (𝕨≥-≠𝕩) ∧ 𝕨<≠𝕩
  𝕨⊑𝕩
}

# ---- arithmetic. Each argument is a number or a flat list; two lists must
# have the same length. Monadic: a number or a flat list.
_ar2 ← {
  "k: arithmetic on non-numbers" Chk (NumOrFlat 𝕨) ∧ NumOrFlat 𝕩
  "k: length mismatch" Chk (1=•Type 𝕨) ∨ (1=•Type 𝕩) ∨ 𝕨 =○≠ 𝕩
  𝕨 𝔽 𝕩
}
_ar1 ← {"k: arithmetic on non-numbers" Chk NumOrFlat 𝕩 ⋄ 𝔽 𝕩}
Add ⇐ + _ar2 ⋄ Sub ⇐ - _ar2 ⋄ Mul ⇐ × _ar2 ⋄ Div ⇐ ÷ _ar2 ⋄ Mod ⇐ | _ar2
Min ⇐ ⌊ _ar2 ⋄ Max ⇐ ⌈ _ar2
Eq ⇐ = _ar2 ⋄ Ne ⇐ ≠ _ar2 ⋄ Lt ⇐ < _ar2 ⋄ Le ⇐ ≤ _ar2 ⋄ Gt ⇐ > _ar2 ⋄ Ge ⇐ ≥ _ar2
Floor ⇐ ⌊ _ar1 ⋄ Abs ⇐ | _ar1

# ---- folds and scans over a flat list
_fl ← {"k: fold or scan needs a flat list" Chk IsFlat 𝕩 ⋄ 𝔽 𝕩}
FoldAdd ⇐ +´_fl ⋄ FoldMul ⇐ ×´_fl ⋄ FoldMax ⇐ ⌈´_fl ⋄ FoldMin ⇐ ⌊´_fl
ScanAdd ⇐ +`_fl ⋄ ScanMax ⇐ ⌈`_fl

# ---- selection
Gather ⇐ {  # 𝕨: flat list of indices (negatives count from the end)
  "k.Gather: 𝕨 must be a flat list" Chk IsFlat 𝕨
  "k.Gather: 𝕩 must be a list" Chk IsList 𝕩
  "k.Gather: index out of bounds" Chk ∧´(𝕨=⌊𝕨) ∧ (𝕨≥-≠𝕩) ∧ 𝕨<≠𝕩
  𝕨⊏𝕩
}
Scatter ⇐ {  # i‿v Scatter 𝕩: copy of 𝕩 with 𝕩[i[j]] = v[j]
  i‿v ← 𝕨
  "k.Scatter: 𝕩 must be a list" Chk IsList 𝕩
  "k.Scatter: i must be a flat list" Chk IsFlat i
  "k.Scatter: v must be a list as long as i" Chk (IsList v) ∧ i =○≠ v
  "k.Scatter: index out of bounds" Chk ∧´(i=⌊i) ∧ (i≥-≠𝕩) ∧ i<≠𝕩
  v⌾(i⊸⊏) 𝕩
}
Compress ⇐ {  # 𝕨: boolean list as long as 𝕩
  "k.Compress: 𝕨 must be a boolean list" Chk (IsFlat 𝕨) ∧ ∧´𝕨∊0‿1
  "k.Compress: 𝕩 must be a list as long as 𝕨" Chk (IsList 𝕩) ∧ 𝕨 =○≠ 𝕩
  𝕨/𝕩
}
Indices ⇐ {  # /𝕩 for a list of naturals
  "k.Indices: 𝕩 must be a list of naturals" Chk (IsFlat 𝕩) ∧ ∧´IsNat¨𝕩
  /𝕩
}

# ---- search and sort. Elements compare as BQN values (≡ and array ordering).
Grade ⇐ {"k.Grade: 𝕩 must be a list" Chk IsList 𝕩 ⋄ ⍋𝕩}
IndexOf ⇐ {   # for each element of 𝕩, its first index in 𝕨, or ≠𝕨
  "k.IndexOf: 𝕨 and 𝕩 must be lists" Chk (IsList 𝕨) ∧ IsList 𝕩
  𝕨⊐𝕩
}
Hist ⇐ {      # n Hist 𝕩: counts of each of ↕n in 𝕩
  "k.Hist: 𝕨 must be a natural number" Chk IsNat 𝕨
  "k.Hist: 𝕩 must be a list of naturals below 𝕨" Chk (IsFlat 𝕩) ∧ ∧´(IsNat¨𝕩) ∧ 𝕩<𝕨
  𝕨↑/⁼𝕩
}
Match ⇐ ≡     # any values

# ---- callbacks. 𝔽 is any function; these are the loops that call it.
_each ⇐ {
  𝔽 _𝕣 𝕩:
    "k._each: 𝕩 must be a list" Chk IsList 𝕩
    𝔽¨ 𝕩
  ;
  𝕨 𝔽 _𝕣 𝕩:
    "k._each: 𝕨 and 𝕩 must be lists of equal length" Chk (IsList 𝕨) ∧ (IsList 𝕩) ∧ 𝕨 =○≠ 𝕩
    𝕨 𝔽¨ 𝕩
}
_fold ⇐ {     # right to left; with 𝕨 as the initial value
  𝔽 _𝕣 𝕩:
    "k._fold: 𝕩 must be a non-empty list" Chk (IsList 𝕩) ∧ 0<≠𝕩
    𝔽´ 𝕩
  ;
  𝕨 𝔽 _𝕣 𝕩:
    "k._fold: 𝕩 must be a list" Chk IsList 𝕩
    𝕨 𝔽´ 𝕩
}
_scan ⇐ {     # left to right, monadic only
  "k._scan: 𝕩 must be a list" Chk IsList 𝕩
  𝔽` 𝕩
}

# ---- markers: opaque atoms that only compare by identity. Used by ⌾ to see
# where a structural function moves elements. Arithmetic on them fails.
Markers ⇐ {"k.Markers: 𝕩 must be a natural number" Chk IsNat 𝕩 ⋄ {𝕩⋄{⇐}}¨↕𝕩}
IsMarker ⇐ {6=•Type 𝕩}
