# prims.bqn: BQN primitives in the primitive dialect (see docs/design.md).
#
# Every glyph here means its definition in this file, and a definition may
# only use glyphs defined above it. Real work happens only in the basis k.
# Check and run with dialect.bqn; test against CBQN with test/prims.bqn.
#
# Not supported yet, and reported as errors: fills (overtake of arrays without
# one, empty ⊑ and >), character arithmetic, list 𝕨 for ⊏ ⌽ / ↑ ↓ (multiple
# axes), ⍷ above rank 1, computational ⌾, and the glyphs with no definition.

k ← •args

# ---- helpers, basis only
Els ← {k.IsArr 𝕩 ? k.Deshape 𝕩 ; ⟨𝕩⟩}          # elements as a list
Lst ← {k.IsArr 𝕩 ? 𝕩 ; ⟨𝕩⟩}
RankOf ← {k.Len k.Shape 𝕩}
CellShape ← {s ← k.Shape 𝕩 ⋄ ⟨1, (k.Len s) k.Sub 1⟩ k.Slice s}
Strides ← {s ← 𝕩 ⋄ r ← k.Len s ⋄ {k.FoldMul ⟨𝕩 k.Add 1, r k.Sub 𝕩 k.Add 1⟩ k.Slice s} k._each k.Range r}
AllNum ← {1 k.Min k.FoldMin (1 k.Eq k.Type) k._each Els 𝕩}

# c CellIdx ix: element indices of the cells ix, each c elements long
CellIdx ← {
  m ← k.Len 𝕩
  rep ← k.Indices 𝕨 k.Add 0 k.Mul k.Range m
  (𝕨 k.Mul rep k.Gather 𝕩) k.Add 𝕨 k.Mod k.Range m k.Mul 𝕨
}
# ix SelCells 𝕩: elements of the major cells ix of 𝕩, as a list
SelCells ← {((k.FoldMul CellShape 𝕩) CellIdx 𝕨) k.Gather k.Deshape 𝕩}
# r KCells 𝕩: frame shape and the list of r-cells, each as an array. An
# atom is its own only cell.
KCells ← {
  𝕨 𝕊 𝕩: 0 k.Eq k.IsArr 𝕩 ? ⟨⟨⟩, ⟨𝕩⟩⟩ ;
  𝕨 𝕊 𝕩:
  s ← k.Shape 𝕩 ⋄ f ← (k.Len s) k.Sub 𝕨
  fs ← ⟨0, f⟩ k.Slice s ⋄ cs ← ⟨f, 𝕨⟩ k.Slice s
  c ← k.FoldMul cs ⋄ d ← Els 𝕩
  ⟨fs, {cs k.Reshape ⟨𝕩 k.Mul c, c⟩ k.Slice d} k._each k.Range k.FoldMul fs⟩
}
MajorCells ← {1 k.Pick ((RankOf 𝕩) k.Sub 1) KCells 𝕩}

# 𝕨 Agree 𝕩: leading-axis agreement. Returns both element lists, extended to
# the result shape, and that shape.
Agree ← {
  ws ← k.Shape 𝕨 ⋄ xs ← k.Shape 𝕩
  wr ← k.Len ws ⋄ xr ← k.Len xs ⋄ r ← wr k.Min xr
  "Mapping: leading axes of the arguments must match" ! (⟨0, r⟩ k.Slice ws) k.Match ⟨0, r⟩ k.Slice xs
  s ← (wr k.Lt xr) k.Pick ⟨ws, xs⟩
  c ← k.FoldMul ⟨r, (k.Len s) k.Sub r⟩ k.Slice s
  Ext ← {(k.Indices c k.Add 0 k.Mul k.Range k.Len 𝕩) k.Gather 𝕩}
  wl ← Els 𝕨 ⋄ xl ← Els 𝕩
  ⟨(wr k.Lt xr) k.Pick ⟨wl, Ext wl⟩, (xr k.Lt wr) k.Pick ⟨xl, Ext xl⟩, s⟩
}

Merge ← {
  𝕊 𝕩: 0 k.Eq k.IsArr 𝕩 ? 𝕩 ;
  𝕊 𝕩: 0 k.Eq k.Count 𝕩 ? 𝕩 ;
  𝕊 𝕩:
    es ← k.Deshape 𝕩
    cs ← k.Shape 0 k.Pick es
    ">: elements must have matching shapes" ! k.FoldMin {cs k.Match k.Shape 𝕩} k._each es
    (k.Cat ⟨k.Shape 𝕩, cs⟩) k.Reshape k.Cat Els k._each es
}

# ---- encodings (see k.bqn). Only lists are encoded. A path that uses an
# encoding must give exactly the plain path's result.
IsList ← {1 k.Eq RankOf 𝕩}
Is ← {(IsList 𝕩) k.Min 𝕨 k.Match k.Enc 𝕩}          # "dict" Is 𝕩
IntAtom ← {1 k.Eq k.Type 𝕩 ? 𝕩 k.Eq k.Floor 𝕩 ; 0}
IntList ← {AllNum 𝕩 ? 1 k.Min k.FoldMin 𝕩 k.Eq k.Floor 𝕩 ; 0}
Affine ← {(𝕩 k.Same k.add) k.Max (𝕩 k.Same k.sub) k.Max 𝕩 k.Same k.mul}

# e 𝔽 _vals 𝕩: 𝔽 𝕩 for an elementwise 𝔽, computed once per stored value
# when list 𝕩 has encoding e, and keeping that encoding
_vals ← {
  𝕨 𝔽 _𝕣 𝕩: 𝕨 k.Match "const" ? v‿n ← "const" k.Parts 𝕩 ⋄ k.MkConst ⟨𝔽 v, n⟩ ;
  𝕨 𝔽 _𝕣 𝕩: 𝕨 k.Match "runs" ? v‿c ← "runs" k.Parts 𝕩 ⋄ k.MkRuns ⟨𝔽 v, c⟩ ;
  𝕨 𝔽 _𝕣 𝕩: 𝕨 k.Match "dict" ? c‿d ← "dict" k.Parts 𝕩 ⋄ k.MkDict ⟨c, 𝔽 d⟩ ;
  𝕨 𝔽 _𝕣 𝕩: 𝔽 𝕩
}

# ---- structure, basis only
Shape ⇐ {𝕊 𝕩: k.Shape 𝕩 ; 𝕨 𝕊 𝕩: 1 k.Sub 𝕨 k.Match 𝕩}

Match ⇐ {
  𝕊 𝕩: k.IsArr 𝕩 ? 1 k.Add 0 k.Max k.FoldMax 𝕊 k._each k.Deshape 𝕩 ;
  𝕊 𝕩: 0 ;
  𝕨 𝕊 𝕩: 𝕨 k.Match 𝕩
}

Reshape ⇐ {
  𝕊 𝕩: Els 𝕩 ;
  𝕨 𝕊 𝕩: (1 k.Eq k.Type 𝕨) k.Min 1 k.Eq k.Count 𝕩 ? k.MkConst ⟨0 k.Pick Els 𝕩, 𝕨⟩ ;
  𝕨 𝕊 𝕩:
    s ← Lst 𝕨 ⋄ d ← Els 𝕩 ⋄ n ← k.FoldMul s ⋄ m ← k.Len d
    "⥊: 𝕩 is empty and fills are not supported" ! (0 k.Lt m) k.Max n k.Eq 0
    s k.Reshape (m k.Mod k.Range n) k.Gather d
}

# 𝕨 Contig 𝕩: 𝕨 is a range of in-bounds, increasing, consecutive indices
Contig ← {"range" Is 𝕨 ? s‿d‿n ← "range" k.Parts 𝕨 ⋄ (d k.Eq 1) k.Min (s k.Ge 0) k.Min (s k.Add n) k.Le k.Len 𝕩 ; 0}
Select ⇐ {
  𝕊 𝕩: 0 𝕊 𝕩 ;
  𝕨 𝕊 𝕩: "dict" Is 𝕩 ?
    ix ← (Els 𝕨) k.Gather k.Range k.Len 𝕩
    c‿d ← "dict" k.Parts 𝕩
    (k.Shape 𝕨) k.Reshape k.MkDict ⟨ix k.Gather c, d⟩ ;
  𝕨 𝕊 𝕩: "const" Is 𝕩 ?
    ix ← (Els 𝕨) k.Gather k.Range k.Len 𝕩
    (k.Shape 𝕨) k.Reshape k.MkConst ⟨0 k.Pick "const" k.Parts 𝕩, k.Len ix⟩ ;
  𝕨 𝕊 𝕩: "range" Is 𝕩 ?
    ix ← (Els 𝕨) k.Gather k.Range k.Len 𝕩
    s‿d‿n ← "range" k.Parts 𝕩
    (k.Shape 𝕨) k.Reshape s k.Add d k.Mul ix ;
  𝕨 𝕊 𝕩: (IsList 𝕩) k.Min 𝕨 Contig 𝕩 ?
    s‿d‿n ← "range" k.Parts 𝕨
    ⟨s, n⟩ k.Slice k.Deshape 𝕩 ;
  𝕨 𝕊 𝕩:
    "⊏: 𝕩 must have rank at least 1" ! 0 k.Lt RankOf 𝕩
    ix ← (Els 𝕨) k.Gather k.Range k.Len 𝕩     # checks bounds, resolves negatives
    (k.Cat ⟨k.Shape 𝕨, CellShape 𝕩⟩) k.Reshape ix SelCells 𝕩
}

Pick ⇐ {
  𝕊 𝕩: k.IsArr 𝕩 ? 0 k.Pick k.Deshape 𝕩 ;
  𝕊 𝕩: 𝕩 ;
  𝕨 𝕊 𝕩: 1 k.Eq k.Type 𝕨 ?
    "⊑: a number 𝕨 needs a list 𝕩" ! 1 k.Eq RankOf 𝕩
    𝕨 k.Pick k.Deshape 𝕩 ;
  𝕨 𝕊 𝕩: (1 k.Eq RankOf 𝕨) k.Min AllNum 𝕨 ?
    s ← k.Shape 𝕩
    "⊑: index length must match the rank of 𝕩" ! (k.Len 𝕨) k.Eq k.Len s
    t ← 𝕨 k.Add s k.Mul 𝕨 k.Lt 0
    "⊑: index out of bounds" ! 1 k.Min k.FoldMin (t k.Ge 0) k.Mul t k.Lt s
    (k.FoldAdd t k.Mul Strides s) k.Pick k.Deshape 𝕩 ;
  𝕨 𝕊 𝕩: (k.Shape 𝕨) k.Reshape 𝕊⟜𝕩 k._each Els 𝕨
}

Range ⇐ {
  𝕊 𝕩: k.IsArr 𝕩 ?
    "↕: 𝕩 must be a number or a list" ! 1 k.Eq RankOf 𝕩
    s ← k.Deshape 𝕩 ⋄ i ← k.Range k.FoldMul s ⋄ st ← Strides s
    digits ← {(𝕩 k.Pick s) k.Mod k.Floor i k.Div 𝕩 k.Pick st} k._each k.Range k.Len s
    s k.Reshape {j ← 𝕩 ⋄ {j k.Pick 𝕩} k._each digits} k._each i ;
  𝕊 𝕩: k.MkRange ⟨0, 1, 𝕩⟩
}

_each ⇐ {
  𝔽 _𝕣 𝕩: (k.Shape 𝕩) k.Reshape 𝔽 k._each Els 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: wl‿xl‿s ← 𝕨 Agree 𝕩 ⋄ s k.Reshape wl 𝔽 k._each xl
}

_table ⇐ {
  𝔽 _𝕣 𝕩: 𝔽¨ 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩:
    wl ← Els 𝕨 ⋄ xl ← Els 𝕩 ⋄ m ← k.Len wl ⋄ n ← k.Len xl
    wi ← k.Indices n k.Add 0 k.Mul k.Range m
    xi ← n k.Mod k.Range m k.Mul n
    (k.Cat ⟨k.Shape 𝕨, k.Shape 𝕩⟩) k.Reshape (wi k.Gather wl) 𝔽 k._each xi k.Gather xl
}

GradeUp ⇐ {
  𝕊 𝕩: k.Sorted 𝕩 ? k.MkRange ⟨0, 1, k.Len 𝕩⟩ ;
  𝕊 𝕩: "const" Is 𝕩 ? k.MkRange ⟨0, 1, k.Len 𝕩⟩ ;
  𝕊 𝕩: "range" Is 𝕩 ?
    s‿d‿n ← "range" k.Parts 𝕩
    (d k.Ge 0) k.Pick ⟨k.MkRange ⟨n k.Sub 1, ¯1, n⟩, k.MkRange ⟨0, 1, n⟩⟩ ;
  𝕊 𝕩: "dict" Is 𝕩 ?   # grade the dictionary, then the codes by rank
    c‿d ← "dict" k.Parts 𝕩
    r ← ((k.Grade d) k.Gather d) k.IndexOf d      # equal entries share a rank
    k.Grade c k.Gather r ;
  𝕊 𝕩:
    "⍋: 𝕩 must have rank at least 1" ! 0 k.Lt RankOf 𝕩
    1 k.Eq RankOf 𝕩 ? k.Grade k.Deshape 𝕩 ;
  𝕊 𝕩: k.Grade MajorCells 𝕩
}

Reverse ⇐ {
  𝕊 𝕩: "range" Is 𝕩 ?
    s‿d‿n ← "range" k.Parts 𝕩
    k.MkRange ⟨s k.Add d k.Mul n k.Sub 1, 0 k.Sub d, n⟩ ;
  𝕊 𝕩: "const" Is 𝕩 ? 𝕩 ;
  𝕊 𝕩: "runs" Is 𝕩 ? v‿c ← "runs" k.Parts 𝕩 ⋄ k.MkRuns ⟨𝕊 v, 𝕊 c⟩ ;
  𝕊 𝕩: "dict" Is 𝕩 ? c‿d ← "dict" k.Parts 𝕩 ⋄ k.MkDict ⟨𝕊 c, d⟩ ;
  𝕊 𝕩:
    "⌽: 𝕩 must have rank at least 1" ! 0 k.Lt RankOf 𝕩
    n ← k.Len 𝕩
    (k.Shape 𝕩) k.Reshape ((n k.Sub 1) k.Sub k.Range n) SelCells 𝕩 ;
  𝕨 𝕊 𝕩:
    "⌽: only a number 𝕨 is supported" ! 1 k.Eq k.Type 𝕨
    "⌽: 𝕩 must have rank at least 1" ! 0 k.Lt RankOf 𝕩
    n ← k.Len 𝕩
    (k.Shape 𝕩) k.Reshape (n k.Mod 𝕨 k.Add k.Range n) SelCells 𝕩
}

# ---- arithmetic. A basis operation applies directly to numbers and flat
# arrays of matching shape; anything else recurses through ¨.
FlatOrAtom ← {k.IsArr 𝕩 ? k.Flat k.Deshape 𝕩 ; 1}
Ev ← {k.IsArr 𝕩 ? k.Deshape 𝕩 ; 𝕩}
_p2f ← {
  𝕨 𝔽 _𝕣 𝕩: 0 k.Eq (k.IsArr 𝕨) k.Max k.IsArr 𝕩 ? 𝕨 𝔽 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩:
    same ← (0 k.Eq k.IsArr 𝕨) k.Max (0 k.Eq k.IsArr 𝕩) k.Max (k.Shape 𝕨) k.Match k.Shape 𝕩
    same k.Min (FlatOrAtom 𝕨) k.Min FlatOrAtom 𝕩 ?
    ((k.IsArr 𝕨) k.Pick ⟨k.Shape 𝕩, k.Shape 𝕨⟩) k.Reshape (Ev 𝕨) 𝔽 Ev 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: 𝕨 𝔽 _𝕣¨ 𝕩
}
_p1f ← {
  𝔽 _𝕣 𝕩: 0 k.Eq k.IsArr 𝕩 ? 𝔽 𝕩 ;
  𝔽 _𝕣 𝕩: k.Flat k.Deshape 𝕩 ? (k.Shape 𝕩) k.Reshape 𝔽 k.Deshape 𝕩 ;
  𝔽 _𝕣 𝕩: 𝔽 _𝕣¨ 𝕩
}
# With encodings: an affine operation moves a range, and any elementwise
# operation between an atom and a const, runs or dict list works on the
# stored values.
_p2 ← {
  𝕨 𝔽 _𝕣 𝕩: (IntAtom 𝕨) k.Min (Affine 𝕗) k.Min "range" Is 𝕩 ?
    s‿d‿n ← "range" k.Parts 𝕩 ⋄ a ← 𝕨 𝔽 s
    k.MkRange ⟨a, (𝕨 𝔽 s k.Add d) k.Sub a, n⟩ ;
  𝕨 𝔽 _𝕣 𝕩: (IntAtom 𝕩) k.Min (Affine 𝕗) k.Min "range" Is 𝕨 ?
    s‿d‿n ← "range" k.Parts 𝕨 ⋄ a ← s 𝔽 𝕩
    k.MkRange ⟨a, ((s k.Add d) 𝔽 𝕩) k.Sub a, n⟩ ;
  𝕨 𝔽 _𝕣 𝕩: (0 k.Eq k.IsArr 𝕨) k.Min IsList 𝕩 ? (k.Enc 𝕩) (𝕨 𝔽 _p2f ⊢) _vals 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: (0 k.Eq k.IsArr 𝕩) k.Min IsList 𝕨 ? (k.Enc 𝕨) (𝔽 _p2f⟜𝕩) _vals 𝕨 ;
  𝕨 𝔽 _𝕣 𝕩: 𝕨 𝔽 _p2f 𝕩
}
_p1 ← {
  𝔽 _𝕣 𝕩: IsList 𝕩 ? (k.Enc 𝕩) (𝔽 _p1f) _vals 𝕩 ;
  𝔽 _𝕣 𝕩: 𝔽 _p1f 𝕩
}

Plus ⇐ {𝕊 𝕩: 0 𝕊 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Add _p2 𝕩}
Minus ⇐ {𝕊 𝕩: 0 𝕊 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Sub _p2 𝕩}
Times ⇐ {𝕊 𝕩: {(0 k.Lt 𝕩) k.Sub 𝕩 k.Lt 0} _p1 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Mul _p2 𝕩}
Divide ⇐ {𝕊 𝕩: 1 𝕊 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Div _p2 𝕩}
Floor ⇐ {𝕊 𝕩: k.Floor _p1 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Min _p2 𝕩}
Ceil ⇐ {𝕊 𝕩: -⌊-𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Max _p2 𝕩}
Abs ⇐ {𝕊 𝕩: k.Abs _p1 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Mod _p2 𝕩}
Not ⇐ {𝕊 𝕩: 1-𝕩 ; 𝕨 𝕊 𝕩: 1+𝕨-𝕩}
Equal ⇐ {𝕊 𝕩: RankOf 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Eq _p2 𝕩}
NotEq ⇐ {𝕊 𝕩: k.Len 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Ne _p2 𝕩}
Less ⇐ {𝕊 𝕩: ⟨⟩ k.Reshape ⟨𝕩⟩ ; 𝕨 𝕊 𝕩: 𝕨 k.Lt _p2 𝕩}
Greater ⇐ {𝕊 𝕩: Merge 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 k.Gt _p2 𝕩}
LessEq ⇐ {𝕨 𝕊 𝕩: 𝕨 k.Le _p2 𝕩}
GreaterEq ⇐ {𝕨 𝕊 𝕩: 𝕨 k.Ge _p2 𝕩}

# ---- from here on, definitions use glyphs
GradeDown ⇐ {𝕊 𝕩: ⌽ (¯1+≠𝕩) - ⍋⌽𝕩}
And ⇐ {𝕊 𝕩: k.Sorted 𝕩 ? 𝕩 ; 𝕊 𝕩: (⍋𝕩)⊏𝕩 ; 𝕨 𝕊 𝕩: 𝕨×𝕩}
Or ⇐ {𝕊 𝕩: (⍒𝕩)⊏𝕩 ; 𝕨 𝕊 𝕩: (𝕨+𝕩)-𝕨×𝕩}

Replicate ⇐ {
  𝕊 𝕩:   # long runs stay run-length encoded
    "/: 𝕩 must be a list" ! 1==𝕩
    x ← k.Deshape 𝕩
    "/: 𝕩 must be natural numbers" ! IntList x
    "/: 𝕩 must be natural numbers" ! 1 k.Min k.FoldMin x k.Ge 0
    nz ← 0 k.Lt x
    (k.FoldAdd x) k.Ge 2 k.Mul k.FoldAdd nz ?
    k.MkRuns ⟨nz k.Compress k.Range ≠x, nz k.Compress x⟩ ;
  𝕊 𝕩: k.Indices k.Deshape 𝕩 ;
  𝕨 𝕊 𝕩: ({IntAtom 𝕩 ? 𝕩 ≥ 1 ; 0} 𝕨) ∧ "runs" Is 𝕩 ?
    v‿c ← "runs" k.Parts 𝕩 ⋄ k.MkRuns ⟨v, 𝕨×c⟩ ;
  𝕨 𝕊 𝕩: "dict" Is 𝕩 ? c‿d ← "dict" k.Parts 𝕩 ⋄ k.MkDict ⟨𝕨 𝕊 c, d⟩ ;
  𝕨 𝕊 𝕩: "const" Is 𝕩 ? v‿n ← "const" k.Parts 𝕩 ⋄ k.MkConst ⟨v, ≠𝕨 𝕊 k.Range n⟩ ;
  𝕨 𝕊 𝕩:
    "/: 𝕩 must have rank at least 1" ! 1≤=𝕩
    n ← ≠𝕩
    c ← {𝕊 w: 0==w ? n⥊w ; 𝕊 w: w} 𝕨
    "/: 𝕨 must be a list with one count per major cell of 𝕩" ! (1==c) ∧ n=≠c
    ix ← k.Indices k.Deshape c
    (k.Cat ⟨⟨≠ix⟩, CellShape 𝕩⟩) k.Reshape ix SelCells 𝕩
}

# Identity of a function for an empty fold. Compares against the dialect's own
# primitives; the compiler resolves this statically.
Identity ← {
  𝕊 f: (f k.Same plus) ∨ (f k.Same minus) ∨ (f k.Same or) ∨ f k.Same notEq ? 0 ;
  𝕊 f: (f k.Same times) ∨ (f k.Same divide) ∨ (f k.Same and) ∨ f k.Same equal ? 1 ;
  𝕊 f: f k.Same floor ? ∞ ;
  𝕊 f: f k.Same ceil ? ¯∞ ;
  𝕊 f: "´: no identity for this function on an empty list" ! 0
}

# Integer encodings, for folds that are exact only on integers
IntConst ← {"const" Is 𝕩 ? IntAtom 0 k.Pick "const" k.Parts 𝕩 ; 0}
IntRuns ← {"runs" Is 𝕩 ? IntList 0 k.Pick "runs" k.Parts 𝕩 ; 0}
IntDict ← {"dict" Is 𝕩 ? IntList 1 k.Pick "dict" k.Parts 𝕩 ; 0}

_fold ⇐ {
  𝔽 _𝕣 𝕩: "´: 𝕩 must be a list" ! 1==𝕩 ⋄ 0=≠𝕩 ? Identity 𝕗 ;
  # +´ on encodings; floats take the plain path, since n×v rounds differently
  # from n additions
  𝔽 _𝕣 𝕩: (𝕗 k.Same plus) ∧ IntConst 𝕩 ? v‿n ← "const" k.Parts 𝕩 ⋄ n×v ;
  𝔽 _𝕣 𝕩: (𝕗 k.Same plus) ∧ "range" Is 𝕩 ? s‿d‿n ← "range" k.Parts 𝕩 ⋄ (n×s) + d × (n×n-1)÷2 ;
  𝔽 _𝕣 𝕩: (𝕗 k.Same plus) ∧ IntRuns 𝕩 ? v‿c ← "runs" k.Parts 𝕩 ⋄ 𝕊 v×c ;
  𝔽 _𝕣 𝕩: (𝕗 k.Same plus) ∧ IntDict 𝕩 ? c‿d ← "dict" k.Parts 𝕩 ⋄ 𝕊 d × (≠d) k.Hist c ;
  # ⌈´ on encodings: the maximum of the stored values that are used
  𝔽 _𝕣 𝕩: (𝕗 k.Same ceil) ∧ "const" Is 𝕩 ? 0 k.Pick "const" k.Parts 𝕩 ;
  𝔽 _𝕣 𝕩: (𝕗 k.Same ceil) ∧ "range" Is 𝕩 ? s‿d‿n ← "range" k.Parts 𝕩 ⋄ s ⌈ s + d×n-1 ;
  𝔽 _𝕣 𝕩: (𝕗 k.Same ceil) ∧ "runs" Is 𝕩 ? 𝕊 0 k.Pick "runs" k.Parts 𝕩 ;
  𝔽 _𝕣 𝕩: (𝕗 k.Same ceil) ∧ "dict" Is 𝕩 ? c‿d ← "dict" k.Parts 𝕩 ⋄ 𝕊 (0 < (≠d) k.Hist c) / d ;
  𝔽 _𝕣 𝕩: (𝕗 k.Same plus) ∧ k.Flat 𝕩 ? k.FoldAdd 𝕩 ;
  𝔽 _𝕣 𝕩: (𝕗 k.Same ceil) ∧ k.Flat 𝕩 ? k.FoldMax 𝕩 ;
  𝔽 _𝕣 𝕩: 𝔽 k._fold k.Deshape 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: "´: 𝕩 must be a list" ! 1==𝕩 ⋄ 𝕨 𝔽 k._fold k.Deshape 𝕩
}

_insert ⇐ {
  𝔽 _𝕣 𝕩: "˝: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ 0=≠𝕩 ? (CellShape 𝕩) ⥊ Identity 𝕗 ;
  𝔽 _𝕣 𝕩: 𝔽 k._fold MajorCells 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: "˝: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ 𝕨 𝔽 k._fold MajorCells 𝕩
}

_scan ⇐ {
  𝔽 _𝕣 𝕩: "`: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ 0=≠𝕩 ? 𝕩 ;
  𝔽 _𝕣 𝕩: (1==𝕩) ∧ (𝕗 k.Same plus) ∧ k.Flat 𝕩 ? k.ScanAdd 𝕩 ;
  𝔽 _𝕣 𝕩: (1==𝕩) ∧ (𝕗 k.Same ceil) ∧ k.Flat 𝕩 ? k.ScanMax 𝕩 ;
  𝔽 _𝕣 𝕩: 1==𝕩 ? 𝔽 k._scan k.Deshape 𝕩 ;
  𝔽 _𝕣 𝕩: > 𝔽 k._scan MajorCells 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: "`: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ 0=≠𝕩 ? 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: 1==𝕩 ?   # 𝕨 is a 0-cell, so a rank-0 array is unwrapped
    "`: 𝕨 must have the shape of a cell of 𝕩" ! 0==𝕨
    ⟨1, ≠𝕩⟩ k.Slice 𝔽 k._scan k.Cat ⟨⟨⊑𝕨⟩, k.Deshape 𝕩⟩ ;
  𝕨 𝔽 _𝕣 𝕩:
    cells ← MajorCells 𝕩
    > ⟨1, ≠cells⟩ k.Slice 𝔽 k._scan k.Cat ⟨⟨𝕨⟩, cells⟩
}

Join ⇐ {
  𝕊 𝕩:
    "∾: only a list 𝕩 is supported" ! 1==𝕩
    "∾: empty 𝕩 needs fills, which are not supported" ! 0<≠𝕩
    𝕊´ 𝕩 ;
  𝕨 𝕊 𝕩:
    wr ← =𝕨 ⋄ xr ← =𝕩 ⋄ r ← 1⌈wr⌈xr
    "∾: ranks of 𝕨 and 𝕩 must differ by at most 1" ! (wr ≥ r-1) ∧ xr ≥ r-1
    Cs ← {𝕊 v: r = =v ? CellShape v ; 𝕊 v: ≢v}
    Ln ← {𝕊 v: r = =v ? ≠v ; 𝕊 v: 1}
    "∾: cell shapes must match" ! (Cs 𝕨) ≡ Cs 𝕩
    (k.Cat ⟨⟨(Ln 𝕨)+Ln 𝕩⟩, Cs 𝕩⟩) k.Reshape k.Cat ⟨Els 𝕨, Els 𝕩⟩
}

Couple ⇐ {𝕊 𝕩: >⟨𝕩⟩ ; 𝕨 𝕊 𝕩: >⟨𝕨, 𝕩⟩}
Pair ⇐ {𝕊 𝕩: ⟨𝕩⟩ ; 𝕨 𝕊 𝕩: ⟨𝕨, 𝕩⟩}

Take ⇐ {
  𝕊 𝕩: "↑: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ (↕1+≠𝕩) 𝕊¨ <𝕩 ;
  𝕨 𝕊 𝕩:
    "↑: only a number 𝕨 is supported" ! 1 k.Eq k.Type 𝕨
    x ← {𝕊 v: 0==v ? ⥊v ; 𝕊 v: v} 𝕩
    n ← ≠x ⋄ m ← |𝕨 ⋄ cs ← CellShape x
    keep ← m⌊n ⋄ pad ← m-keep
    kept ← (((𝕨<0) ⊑ ⟨0, n-keep⟩) + ↕keep) SelCells x
    fill ← (pad × ×´cs) ⥊ < {𝕊 p: 0<p ? k.Fill k.Deshape x ; 𝕊 p: 0} pad
    (k.Cat ⟨⟨m⟩, cs⟩) k.Reshape k.Cat (𝕨<0) ⊑ ⟨⟨kept, fill⟩, ⟨fill, kept⟩⟩
}

Drop ⇐ {
  𝕊 𝕩: "↓: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ (↕1+≠𝕩) 𝕊¨ <𝕩 ;
  𝕨 𝕊 𝕩:
    "↓: only a number 𝕨 is supported" ! 1 k.Eq k.Type 𝕨
    x ← {𝕊 v: 0==v ? ⥊v ; 𝕊 v: v} 𝕩
    n ← ≠x ⋄ t ← n - n⌊|𝕨
    ((𝕨<0) ⊑ ⟨-t, t⟩) ↑ x
}

IndexOf ⇐ {
  𝕊 𝕩:
    "⊐: 𝕩 must have rank at least 1" ! 1≤=𝕩
    f ← 𝕩 𝕊 𝕩
    f ⊏ (+`f = ↕≠𝕩) - 1 ;
  # searching for encoded values: search for each stored value once
  𝕨 𝕊 𝕩: (1==𝕨) ∧ "dict" Is 𝕩 ? c‿d ← "dict" k.Parts 𝕩 ⋄ k.MkDict ⟨c, 𝕨 𝕊 d⟩ ;
  𝕨 𝕊 𝕩: (1==𝕨) ∧ "runs" Is 𝕩 ? v‿c ← "runs" k.Parts 𝕩 ⋄ k.MkRuns ⟨𝕨 𝕊 v, c⟩ ;
  𝕨 𝕊 𝕩: (1==𝕨) ∧ "const" Is 𝕩 ? v‿n ← "const" k.Parts 𝕩 ⋄ k.MkConst ⟨0 k.Pick 𝕨 𝕊 ⟨v⟩, n⟩ ;
  𝕨 𝕊 𝕩:
    "⊐: 𝕨 must have rank at least 1" ! 1≤=𝕨
    c ← (=𝕨)-1
    "⊐: 𝕩 must have rank at least that of a cell of 𝕨" ! c ≤ =𝕩
    0=c ? (≢𝕩) k.Reshape (k.Deshape 𝕨) k.IndexOf Els 𝕩 ;
  𝕨 𝕊 𝕩:
    c ← (=𝕨)-1
    fs‿xl ← c KCells 𝕩
    fs k.Reshape (MajorCells 𝕨) k.IndexOf xl
}

Member ⇐ {
  𝕊 𝕩: "∊: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ (𝕩⊐𝕩) = ↕≠𝕩 ;
  𝕨 𝕊 𝕩: (1==𝕩) ∧ "dict" Is 𝕨 ? c‿d ← "dict" k.Parts 𝕨 ⋄ k.MkDict ⟨c, d 𝕊 𝕩⟩ ;
  𝕨 𝕊 𝕩: (1==𝕩) ∧ "runs" Is 𝕨 ? v‿c ← "runs" k.Parts 𝕨 ⋄ k.MkRuns ⟨v 𝕊 𝕩, c⟩ ;
  𝕨 𝕊 𝕩: (𝕩⊐𝕨) < ≠𝕩
}

Find ⇐ {
  𝕊 𝕩: (∊𝕩)/𝕩 ;
  𝕨 𝕊 𝕩:
    "⍷: only lists are supported" ! (1==𝕨) ∧ 1==𝕩
    p ← 𝕨 ⋄ t ← 𝕩 ⋄ w ← 0 ⌈ 1+(≠t)-≠p
    (w⥊1) {𝕩 ∧ (𝕨⊑p) ≡¨ (𝕨+↕w)⊏t}´ ↕≠p
}

Group ⇐ {
  𝕊 𝕩: "⊔: only a list 𝕩 is supported" ! 1==𝕩 ⋄ 𝕩 𝕊 ↕≠𝕩 ;
  𝕨 𝕊 𝕩:
    "⊔: only a list 𝕨 is supported" ! 1==𝕨
    "⊔: 𝕩 must have rank at least 1" ! 1≤=𝕩
    n ← ≠𝕩 ⋄ l ← ≠𝕨
    "⊔: 𝕨 must have ≠𝕩 or 1+≠𝕩 elements" ! (l=n) ∨ l=n+1
    keys ← n↑𝕨 ⋄ extra ← 0 ⌈´ n↓𝕨
    "⊔: 𝕨 must be integers at least ¯1" ! ∧´ (keys ≥ ¯1) ∧ keys = ⌊keys
    keep ← keys ≥ 0
    kk ← keep/keys ⋄ ids ← keep/↕n
    g ← extra ⌈ 1 + ¯1 ⌈´ kk
    counts ← g k.Hist kk
    ord ← (⍋kk) ⊏ ids
    t ← 𝕩
    ((+`counts)-counts) {((𝕨+↕𝕩)⊏ord) ⊏ t}¨ counts
}

# Effective cell rank of a value with rank 𝕨, for rank number 𝕩
Eff ← {(𝕩≥0) ⊑ ⟨0⌈𝕨+𝕩, 𝕨⌊𝕩⟩}

# A cell of fills with the shape of the r-cells of 𝕩. With an empty frame, ⎉
# applies 𝔽 to one to find the shape of a result cell.
FillCell ← {(⟨(=𝕩)-𝕨, 𝕨⟩ k.Slice ≢𝕩) ⥊ < k.Fill ⥊𝕩}

_rank_ ⇐ {
  𝔽 _𝕣_ 𝔾 𝕩:
    l ← ⥊ 𝔾 𝕩
    c ← (=𝕩) Eff (((≠l)-1) ⊑ 0‿1‿0) ⊑ l
    fs‿cl ← c KCells 𝕩
    0 = ×´fs ? (fs ∾ ≢ 𝔽 c FillCell 𝕩) k.Reshape ⟨⟩ ;
  𝔽 _𝕣_ 𝔾 𝕩:
    l ← ⥊ 𝔾 𝕩
    c ← (=𝕩) Eff (((≠l)-1) ⊑ 0‿1‿0) ⊑ l
    fs‿cl ← c KCells 𝕩
    > fs ⥊ 𝔽 k._each cl ;
  𝕨 𝔽 _𝕣_ 𝔾 𝕩:
    l ← ⥊ 𝕨 𝔾 𝕩
    rw‿rx ← (((≠l)-1) ⊑ ⟨0‿0, 0‿1, 1‿2⟩) ⊏ l
    cw ← (=𝕨) Eff rw ⋄ cx ← (=𝕩) Eff rx
    fw‿wl ← cw KCells 𝕨
    fx‿xl ← cx KCells 𝕩
    fs ← (fw <○≠ fx) ⊑ ⟨fw, fx⟩
    "Mapping: leading axes of the frames must match" ! fw ≡○((fw ⌊○≠ fx)⊸↑) fx
    0 = ×´fs ? (fs ∾ ≢ (cw FillCell 𝕨) 𝔽 cx FillCell 𝕩) k.Reshape ⟨⟩ ;
  𝕨 𝔽 _𝕣_ 𝔾 𝕩:
    l ← ⥊ 𝕨 𝔾 𝕩
    rw‿rx ← (((≠l)-1) ⊑ ⟨0‿0, 0‿1, 1‿2⟩) ⊏ l
    fw‿wl ← ((=𝕨) Eff rw) KCells 𝕨
    fx‿xl ← ((=𝕩) Eff rx) KCells 𝕩
    > (fw⥊wl) 𝔽¨ fx⥊xl
}

_cells ⇐ {𝔽⎉¯1}

# Structural under: 𝔾 is applied to an array of markers, and the markers it
# returns show which elements of 𝕩 its result came from. 𝔾 that computes on
# values fails on the markers, since computational under is not supported.
Walk ← {   # g Walk v: the markers in g, and the values at the same places in v
  g 𝕊 v: k.IsMarker g ? ⟨⟨g⟩, ⟨v⟩⟩ ;
  g 𝕊 v: 0 k.Eq k.IsArr g ? "⌾: 𝔽 changed a value that 𝔾 created" ! g ≡ v ⋄ ⟨⟨⟩, ⟨⟩⟩ ;
  g 𝕊 v:
    "⌾: 𝔽 must not change the shape of 𝔾's result" ! (k.IsArr v) ∧ (≢g) ≡ ≢v
    parts ← (Els g) 𝕊¨ Els v
    ⟨k.Cat ⊑¨parts, k.Cat 1⊑¨parts⟩
}
_put ← {   # v 𝔽 _put 𝕩: 𝕩 with the elements in 𝔽 𝕩 replaced by v
  "⌾: only an array 𝕩 is supported" ! k.IsArr 𝕩
  mk ← (≢𝕩) ⥊ k.Markers k.Count 𝕩
  m‿vals ← (𝔽 mk) Walk 𝕨
  (≢𝕩) ⥊ ⟨(k.Deshape mk) k.IndexOf m, vals⟩ k.Scatter Els 𝕩
}
_under_ ⇐ {
  𝔽 _𝕣_ 𝔾 𝕩: (𝔽 𝔾 𝕩) 𝔾 _put 𝕩 ;
  𝕨 𝔽 _𝕣_ 𝔾 𝕩: ((𝔾 𝕨) 𝔽 𝔾 𝕩) 𝔾 _put 𝕩
}
