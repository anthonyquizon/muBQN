# prims.bqn: BQN primitives in the primitive dialect (see docs/design.md).
#
# Every glyph here means its definition in this file, and a definition may
# only use glyphs defined above it. Real work happens only in the basis b.
# Check and run with dialect.bqn; test against CBQN with test/prims.bqn.
#
# Not supported yet, and reported as errors: fills (overtake of arrays without
# one, empty ⊑ and >), character arithmetic, list 𝕨 for ⊏ ⌽ / ↑ ↓ (multiple
# axes), ⍷ above rank 1, computational ⌾, and the glyphs with no definition.

b ← •args

# ---- helpers, basis only
Els ← {b.IsArr 𝕩 ? b.Deshape 𝕩 ; ⟨𝕩⟩}          # elements as a list
Lst ← {b.IsArr 𝕩 ? 𝕩 ; ⟨𝕩⟩}
RankOf ← {b.Len b.Shape 𝕩}
CellShape ← {s ← b.Shape 𝕩 ⋄ ⟨1, (b.Len s) b.Sub 1⟩ b.Slice s}
Strides ← {s ← 𝕩 ⋄ r ← b.Len s ⋄ {b.FoldMul ⟨𝕩 b.Add 1, r b.Sub 𝕩 b.Add 1⟩ b.Slice s} b._each b.Range r}
AllNum ← {1 b.Min b.FoldMin (1 b.Eq b.Type) b._each Els 𝕩}

# c CellIdx ix: element indices of the cells ix, each c elements long
CellIdx ← {
  m ← b.Len 𝕩
  rep ← b.Indices 𝕨 b.Add 0 b.Mul b.Range m
  (𝕨 b.Mul rep b.Gather 𝕩) b.Add 𝕨 b.Mod b.Range m b.Mul 𝕨
}
# ix SelCells 𝕩: elements of the major cells ix of 𝕩, as a list
SelCells ← {((b.FoldMul CellShape 𝕩) CellIdx 𝕨) b.Gather b.Deshape 𝕩}
# r KCells 𝕩: frame shape and the list of r-cells, each as an array. An
# atom is its own only cell.
KCells ← {
  𝕨 𝕊 𝕩: 0 b.Eq b.IsArr 𝕩 ? ⟨⟨⟩, ⟨𝕩⟩⟩ ;
  𝕨 𝕊 𝕩:
  s ← b.Shape 𝕩 ⋄ f ← (b.Len s) b.Sub 𝕨
  fs ← ⟨0, f⟩ b.Slice s ⋄ cs ← ⟨f, 𝕨⟩ b.Slice s
  c ← b.FoldMul cs ⋄ d ← Els 𝕩
  ⟨fs, {cs b.Reshape ⟨𝕩 b.Mul c, c⟩ b.Slice d} b._each b.Range b.FoldMul fs⟩
}
MajorCells ← {1 b.Pick ((RankOf 𝕩) b.Sub 1) KCells 𝕩}

# 𝕨 Agree 𝕩: leading-axis agreement. Returns both element lists, extended to
# the result shape, and that shape.
Agree ← {
  ws ← b.Shape 𝕨 ⋄ xs ← b.Shape 𝕩
  wr ← b.Len ws ⋄ xr ← b.Len xs ⋄ r ← wr b.Min xr
  "Mapping: leading axes of the arguments must match" ! (⟨0, r⟩ b.Slice ws) b.Match ⟨0, r⟩ b.Slice xs
  s ← (wr b.Lt xr) b.Pick ⟨ws, xs⟩
  c ← b.FoldMul ⟨r, (b.Len s) b.Sub r⟩ b.Slice s
  Ext ← {(b.Indices c b.Add 0 b.Mul b.Range b.Len 𝕩) b.Gather 𝕩}
  wl ← Els 𝕨 ⋄ xl ← Els 𝕩
  ⟨(wr b.Lt xr) b.Pick ⟨wl, Ext wl⟩, (xr b.Lt wr) b.Pick ⟨xl, Ext xl⟩, s⟩
}

Merge ← {
  𝕊 𝕩: 0 b.Eq b.IsArr 𝕩 ? 𝕩 ;
  𝕊 𝕩: 0 b.Eq b.Count 𝕩 ? 𝕩 ;
  𝕊 𝕩:
    es ← b.Deshape 𝕩
    cs ← b.Shape 0 b.Pick es
    ">: elements must have matching shapes" ! b.FoldMin {cs b.Match b.Shape 𝕩} b._each es
    (b.Cat ⟨b.Shape 𝕩, cs⟩) b.Reshape b.Cat Els b._each es
}

# ---- encodings (see b.bqn). Only lists are encoded. A path that uses an
# encoding must give exactly the plain path's result.
IsList ← {1 b.Eq RankOf 𝕩}
Is ← {(IsList 𝕩) b.Min 𝕨 b.Match b.Enc 𝕩}          # "dict" Is 𝕩
IntAtom ← {1 b.Eq b.Type 𝕩 ? 𝕩 b.Eq b.Floor 𝕩 ; 0}
IntList ← {AllNum 𝕩 ? 1 b.Min b.FoldMin 𝕩 b.Eq b.Floor 𝕩 ; 0}
Affine ← {(𝕩 b.Same b.add) b.Max (𝕩 b.Same b.sub) b.Max 𝕩 b.Same b.mul}

# e 𝔽 _vals 𝕩: 𝔽 𝕩 for an elementwise 𝔽, computed once per stored value
# when list 𝕩 has encoding e, and keeping that encoding
_vals ← {
  𝕨 𝔽 _𝕣 𝕩: 𝕨 b.Match "const" ? v‿n ← "const" b.Parts 𝕩 ⋄ b.MkConst ⟨𝔽 v, n⟩ ;
  𝕨 𝔽 _𝕣 𝕩: 𝕨 b.Match "runs" ? v‿c ← "runs" b.Parts 𝕩 ⋄ b.MkRuns ⟨𝔽 v, c⟩ ;
  𝕨 𝔽 _𝕣 𝕩: 𝕨 b.Match "dict" ? c‿d ← "dict" b.Parts 𝕩 ⋄ b.MkDict ⟨c, 𝔽 d⟩ ;
  𝕨 𝔽 _𝕣 𝕩: 𝔽 𝕩
}

# ---- structure, basis only
Shape ⇐ {𝕊 𝕩: b.Shape 𝕩 ; 𝕨 𝕊 𝕩: 1 b.Sub 𝕨 b.Match 𝕩}

Match ⇐ {
  𝕊 𝕩: b.IsArr 𝕩 ? 1 b.Add 0 b.Max b.FoldMax 𝕊 b._each b.Deshape 𝕩 ;
  𝕊 𝕩: 0 ;
  𝕨 𝕊 𝕩: 𝕨 b.Match 𝕩
}

Reshape ⇐ {
  𝕊 𝕩: Els 𝕩 ;
  𝕨 𝕊 𝕩: (1 b.Eq b.Type 𝕨) b.Min 1 b.Eq b.Count 𝕩 ? b.MkConst ⟨0 b.Pick Els 𝕩, 𝕨⟩ ;
  𝕨 𝕊 𝕩:
    s ← Lst 𝕨 ⋄ d ← Els 𝕩 ⋄ n ← b.FoldMul s ⋄ m ← b.Len d
    "⥊: 𝕩 is empty and fills are not supported" ! (0 b.Lt m) b.Max n b.Eq 0
    s b.Reshape (m b.Mod b.Range n) b.Gather d
}

# 𝕨 Contig 𝕩: 𝕨 is a range of in-bounds, increasing, consecutive indices
Contig ← {"range" Is 𝕨 ? s‿d‿n ← "range" b.Parts 𝕨 ⋄ (d b.Eq 1) b.Min (s b.Ge 0) b.Min (s b.Add n) b.Le b.Len 𝕩 ; 0}
Select ⇐ {
  𝕊 𝕩: 0 𝕊 𝕩 ;
  𝕨 𝕊 𝕩: "dict" Is 𝕩 ?
    ix ← (Els 𝕨) b.Gather b.Range b.Len 𝕩
    c‿d ← "dict" b.Parts 𝕩
    (b.Shape 𝕨) b.Reshape b.MkDict ⟨ix b.Gather c, d⟩ ;
  𝕨 𝕊 𝕩: "const" Is 𝕩 ?
    ix ← (Els 𝕨) b.Gather b.Range b.Len 𝕩
    (b.Shape 𝕨) b.Reshape b.MkConst ⟨0 b.Pick "const" b.Parts 𝕩, b.Len ix⟩ ;
  𝕨 𝕊 𝕩: "range" Is 𝕩 ?
    ix ← (Els 𝕨) b.Gather b.Range b.Len 𝕩
    s‿d‿n ← "range" b.Parts 𝕩
    (b.Shape 𝕨) b.Reshape s b.Add d b.Mul ix ;
  𝕨 𝕊 𝕩: (IsList 𝕩) b.Min 𝕨 Contig 𝕩 ?
    s‿d‿n ← "range" b.Parts 𝕨
    ⟨s, n⟩ b.Slice b.Deshape 𝕩 ;
  𝕨 𝕊 𝕩:
    "⊏: 𝕩 must have rank at least 1" ! 0 b.Lt RankOf 𝕩
    ix ← (Els 𝕨) b.Gather b.Range b.Len 𝕩     # checks bounds, resolves negatives
    (b.Cat ⟨b.Shape 𝕨, CellShape 𝕩⟩) b.Reshape ix SelCells 𝕩
}

Pick ⇐ {
  𝕊 𝕩: b.IsArr 𝕩 ? 0 b.Pick b.Deshape 𝕩 ;
  𝕊 𝕩: 𝕩 ;
  𝕨 𝕊 𝕩: 1 b.Eq b.Type 𝕨 ?
    "⊑: a number 𝕨 needs a list 𝕩" ! 1 b.Eq RankOf 𝕩
    𝕨 b.Pick b.Deshape 𝕩 ;
  𝕨 𝕊 𝕩: (1 b.Eq RankOf 𝕨) b.Min AllNum 𝕨 ?
    s ← b.Shape 𝕩
    "⊑: index length must match the rank of 𝕩" ! (b.Len 𝕨) b.Eq b.Len s
    t ← 𝕨 b.Add s b.Mul 𝕨 b.Lt 0
    "⊑: index out of bounds" ! 1 b.Min b.FoldMin (t b.Ge 0) b.Mul t b.Lt s
    (b.FoldAdd t b.Mul Strides s) b.Pick b.Deshape 𝕩 ;
  𝕨 𝕊 𝕩: (b.Shape 𝕨) b.Reshape 𝕊⟜𝕩 b._each Els 𝕨
}

Range ⇐ {
  𝕊 𝕩: b.IsArr 𝕩 ?
    "↕: 𝕩 must be a number or a list" ! 1 b.Eq RankOf 𝕩
    s ← b.Deshape 𝕩 ⋄ i ← b.Range b.FoldMul s ⋄ st ← Strides s
    digits ← {(𝕩 b.Pick s) b.Mod b.Floor i b.Div 𝕩 b.Pick st} b._each b.Range b.Len s
    s b.Reshape {j ← 𝕩 ⋄ {j b.Pick 𝕩} b._each digits} b._each i ;
  𝕊 𝕩: b.MkRange ⟨0, 1, 𝕩⟩
}

_each ⇐ {
  𝔽 _𝕣 𝕩: (b.Shape 𝕩) b.Reshape 𝔽 b._each Els 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: wl‿xl‿s ← 𝕨 Agree 𝕩 ⋄ s b.Reshape wl 𝔽 b._each xl
}

_table ⇐ {
  𝔽 _𝕣 𝕩: 𝔽¨ 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩:
    wl ← Els 𝕨 ⋄ xl ← Els 𝕩 ⋄ m ← b.Len wl ⋄ n ← b.Len xl
    wi ← b.Indices n b.Add 0 b.Mul b.Range m
    xi ← n b.Mod b.Range m b.Mul n
    (b.Cat ⟨b.Shape 𝕨, b.Shape 𝕩⟩) b.Reshape (wi b.Gather wl) 𝔽 b._each xi b.Gather xl
}

GradeUp ⇐ {
  𝕊 𝕩: b.Sorted 𝕩 ? b.MkRange ⟨0, 1, b.Len 𝕩⟩ ;
  𝕊 𝕩: "const" Is 𝕩 ? b.MkRange ⟨0, 1, b.Len 𝕩⟩ ;
  𝕊 𝕩: "range" Is 𝕩 ?
    s‿d‿n ← "range" b.Parts 𝕩
    (d b.Ge 0) b.Pick ⟨b.MkRange ⟨n b.Sub 1, ¯1, n⟩, b.MkRange ⟨0, 1, n⟩⟩ ;
  𝕊 𝕩: "dict" Is 𝕩 ?   # grade the dictionary, then the codes by rank
    c‿d ← "dict" b.Parts 𝕩
    r ← ((b.Grade d) b.Gather d) b.IndexOf d      # equal entries share a rank
    b.Grade c b.Gather r ;
  𝕊 𝕩:
    "⍋: 𝕩 must have rank at least 1" ! 0 b.Lt RankOf 𝕩
    1 b.Eq RankOf 𝕩 ? b.Grade b.Deshape 𝕩 ;
  𝕊 𝕩: b.Grade MajorCells 𝕩
}

Reverse ⇐ {
  𝕊 𝕩: "range" Is 𝕩 ?
    s‿d‿n ← "range" b.Parts 𝕩
    b.MkRange ⟨s b.Add d b.Mul n b.Sub 1, 0 b.Sub d, n⟩ ;
  𝕊 𝕩: "const" Is 𝕩 ? 𝕩 ;
  𝕊 𝕩: "runs" Is 𝕩 ? v‿c ← "runs" b.Parts 𝕩 ⋄ b.MkRuns ⟨𝕊 v, 𝕊 c⟩ ;
  𝕊 𝕩: "dict" Is 𝕩 ? c‿d ← "dict" b.Parts 𝕩 ⋄ b.MkDict ⟨𝕊 c, d⟩ ;
  𝕊 𝕩:
    "⌽: 𝕩 must have rank at least 1" ! 0 b.Lt RankOf 𝕩
    n ← b.Len 𝕩
    (b.Shape 𝕩) b.Reshape ((n b.Sub 1) b.Sub b.Range n) SelCells 𝕩 ;
  𝕨 𝕊 𝕩:
    "⌽: only a number 𝕨 is supported" ! 1 b.Eq b.Type 𝕨
    "⌽: 𝕩 must have rank at least 1" ! 0 b.Lt RankOf 𝕩
    n ← b.Len 𝕩
    (b.Shape 𝕩) b.Reshape (n b.Mod 𝕨 b.Add b.Range n) SelCells 𝕩
}

# ---- arithmetic. A basis operation applies directly to numbers and flat
# arrays of matching shape; anything else recurses through ¨.
FlatOrAtom ← {b.IsArr 𝕩 ? b.Flat b.Deshape 𝕩 ; 1}
Ev ← {b.IsArr 𝕩 ? b.Deshape 𝕩 ; 𝕩}
_p2f ← {
  𝕨 𝔽 _𝕣 𝕩: 0 b.Eq (b.IsArr 𝕨) b.Max b.IsArr 𝕩 ? 𝕨 𝔽 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩:
    same ← (0 b.Eq b.IsArr 𝕨) b.Max (0 b.Eq b.IsArr 𝕩) b.Max (b.Shape 𝕨) b.Match b.Shape 𝕩
    same b.Min (FlatOrAtom 𝕨) b.Min FlatOrAtom 𝕩 ?
    ((b.IsArr 𝕨) b.Pick ⟨b.Shape 𝕩, b.Shape 𝕨⟩) b.Reshape (Ev 𝕨) 𝔽 Ev 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: 𝕨 𝔽 _𝕣¨ 𝕩
}
_p1f ← {
  𝔽 _𝕣 𝕩: 0 b.Eq b.IsArr 𝕩 ? 𝔽 𝕩 ;
  𝔽 _𝕣 𝕩: b.Flat b.Deshape 𝕩 ? (b.Shape 𝕩) b.Reshape 𝔽 b.Deshape 𝕩 ;
  𝔽 _𝕣 𝕩: 𝔽 _𝕣¨ 𝕩
}
# With encodings: an affine operation moves a range, and any elementwise
# operation between an atom and a const, runs or dict list works on the
# stored values.
_p2 ← {
  𝕨 𝔽 _𝕣 𝕩: (IntAtom 𝕨) b.Min (Affine 𝕗) b.Min "range" Is 𝕩 ?
    s‿d‿n ← "range" b.Parts 𝕩 ⋄ a ← 𝕨 𝔽 s
    b.MkRange ⟨a, (𝕨 𝔽 s b.Add d) b.Sub a, n⟩ ;
  𝕨 𝔽 _𝕣 𝕩: (IntAtom 𝕩) b.Min (Affine 𝕗) b.Min "range" Is 𝕨 ?
    s‿d‿n ← "range" b.Parts 𝕨 ⋄ a ← s 𝔽 𝕩
    b.MkRange ⟨a, ((s b.Add d) 𝔽 𝕩) b.Sub a, n⟩ ;
  𝕨 𝔽 _𝕣 𝕩: (0 b.Eq b.IsArr 𝕨) b.Min IsList 𝕩 ? (b.Enc 𝕩) (𝕨 𝔽 _p2f ⊢) _vals 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: (0 b.Eq b.IsArr 𝕩) b.Min IsList 𝕨 ? (b.Enc 𝕨) (𝔽 _p2f⟜𝕩) _vals 𝕨 ;
  𝕨 𝔽 _𝕣 𝕩: 𝕨 𝔽 _p2f 𝕩
}
_p1 ← {
  𝔽 _𝕣 𝕩: IsList 𝕩 ? (b.Enc 𝕩) (𝔽 _p1f) _vals 𝕩 ;
  𝔽 _𝕣 𝕩: 𝔽 _p1f 𝕩
}

Plus ⇐ {𝕊 𝕩: 0 𝕊 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Add _p2 𝕩}
Minus ⇐ {𝕊 𝕩: 0 𝕊 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Sub _p2 𝕩}
Times ⇐ {𝕊 𝕩: {(0 b.Lt 𝕩) b.Sub 𝕩 b.Lt 0} _p1 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Mul _p2 𝕩}
Divide ⇐ {𝕊 𝕩: 1 𝕊 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Div _p2 𝕩}
Floor ⇐ {𝕊 𝕩: b.Floor _p1 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Min _p2 𝕩}
Ceil ⇐ {𝕊 𝕩: -⌊-𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Max _p2 𝕩}
Abs ⇐ {𝕊 𝕩: b.Abs _p1 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Mod _p2 𝕩}
Not ⇐ {𝕊 𝕩: 1-𝕩 ; 𝕨 𝕊 𝕩: 1+𝕨-𝕩}
Equal ⇐ {𝕊 𝕩: RankOf 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Eq _p2 𝕩}
NotEq ⇐ {𝕊 𝕩: b.Len 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Ne _p2 𝕩}
Less ⇐ {𝕊 𝕩: ⟨⟩ b.Reshape ⟨𝕩⟩ ; 𝕨 𝕊 𝕩: 𝕨 b.Lt _p2 𝕩}
Greater ⇐ {𝕊 𝕩: Merge 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 b.Gt _p2 𝕩}
LessEq ⇐ {𝕨 𝕊 𝕩: 𝕨 b.Le _p2 𝕩}
GreaterEq ⇐ {𝕨 𝕊 𝕩: 𝕨 b.Ge _p2 𝕩}

# ---- from here on, definitions use glyphs
GradeDown ⇐ {𝕊 𝕩: ⌽ (¯1+≠𝕩) - ⍋⌽𝕩}
And ⇐ {𝕊 𝕩: b.Sorted 𝕩 ? 𝕩 ; 𝕊 𝕩: (⍋𝕩)⊏𝕩 ; 𝕨 𝕊 𝕩: 𝕨×𝕩}
Or ⇐ {𝕊 𝕩: (⍒𝕩)⊏𝕩 ; 𝕨 𝕊 𝕩: (𝕨+𝕩)-𝕨×𝕩}

Replicate ⇐ {
  𝕊 𝕩:   # long runs stay run-length encoded
    "/: 𝕩 must be a list" ! 1==𝕩
    x ← b.Deshape 𝕩
    "/: 𝕩 must be natural numbers" ! IntList x
    "/: 𝕩 must be natural numbers" ! 1 b.Min b.FoldMin x b.Ge 0
    nz ← 0 b.Lt x
    (b.FoldAdd x) b.Ge 2 b.Mul b.FoldAdd nz ?
    b.MkRuns ⟨nz b.Compress b.Range ≠x, nz b.Compress x⟩ ;
  𝕊 𝕩: b.Indices b.Deshape 𝕩 ;
  𝕨 𝕊 𝕩: ({IntAtom 𝕩 ? 𝕩 ≥ 1 ; 0} 𝕨) ∧ "runs" Is 𝕩 ?
    v‿c ← "runs" b.Parts 𝕩 ⋄ b.MkRuns ⟨v, 𝕨×c⟩ ;
  𝕨 𝕊 𝕩: "dict" Is 𝕩 ? c‿d ← "dict" b.Parts 𝕩 ⋄ b.MkDict ⟨𝕨 𝕊 c, d⟩ ;
  𝕨 𝕊 𝕩: "const" Is 𝕩 ? v‿n ← "const" b.Parts 𝕩 ⋄ b.MkConst ⟨v, ≠𝕨 𝕊 b.Range n⟩ ;
  𝕨 𝕊 𝕩:
    "/: 𝕩 must have rank at least 1" ! 1≤=𝕩
    n ← ≠𝕩
    c ← {𝕊 w: 0==w ? n⥊w ; 𝕊 w: w} 𝕨
    "/: 𝕨 must be a list with one count per major cell of 𝕩" ! (1==c) ∧ n=≠c
    ix ← b.Indices b.Deshape c
    (b.Cat ⟨⟨≠ix⟩, CellShape 𝕩⟩) b.Reshape ix SelCells 𝕩
}

# Identity of a function for an empty fold. Compares against the dialect's own
# primitives; the compiler resolves this statically.
Identity ← {
  𝕊 f: (f b.Same plus) ∨ (f b.Same minus) ∨ (f b.Same or) ∨ f b.Same notEq ? 0 ;
  𝕊 f: (f b.Same times) ∨ (f b.Same divide) ∨ (f b.Same and) ∨ f b.Same equal ? 1 ;
  𝕊 f: f b.Same floor ? ∞ ;
  𝕊 f: f b.Same ceil ? ¯∞ ;
  𝕊 f: "´: no identity for this function on an empty list" ! 0
}

# Integer encodings, for folds that are exact only on integers
IntConst ← {"const" Is 𝕩 ? IntAtom 0 b.Pick "const" b.Parts 𝕩 ; 0}
IntRuns ← {"runs" Is 𝕩 ? IntList 0 b.Pick "runs" b.Parts 𝕩 ; 0}
IntDict ← {"dict" Is 𝕩 ? IntList 1 b.Pick "dict" b.Parts 𝕩 ; 0}

_fold ⇐ {
  𝔽 _𝕣 𝕩: "´: 𝕩 must be a list" ! 1==𝕩 ⋄ 0=≠𝕩 ? Identity 𝕗 ;
  # +´ on encodings; floats take the plain path, since n×v rounds differently
  # from n additions
  𝔽 _𝕣 𝕩: (𝕗 b.Same plus) ∧ IntConst 𝕩 ? v‿n ← "const" b.Parts 𝕩 ⋄ n×v ;
  𝔽 _𝕣 𝕩: (𝕗 b.Same plus) ∧ "range" Is 𝕩 ? s‿d‿n ← "range" b.Parts 𝕩 ⋄ (n×s) + d × (n×n-1)÷2 ;
  𝔽 _𝕣 𝕩: (𝕗 b.Same plus) ∧ IntRuns 𝕩 ? v‿c ← "runs" b.Parts 𝕩 ⋄ 𝕊 v×c ;
  𝔽 _𝕣 𝕩: (𝕗 b.Same plus) ∧ IntDict 𝕩 ? c‿d ← "dict" b.Parts 𝕩 ⋄ 𝕊 d × (≠d) b.Hist c ;
  # ⌈´ on encodings: the maximum of the stored values that are used
  𝔽 _𝕣 𝕩: (𝕗 b.Same ceil) ∧ "const" Is 𝕩 ? 0 b.Pick "const" b.Parts 𝕩 ;
  𝔽 _𝕣 𝕩: (𝕗 b.Same ceil) ∧ "range" Is 𝕩 ? s‿d‿n ← "range" b.Parts 𝕩 ⋄ s ⌈ s + d×n-1 ;
  𝔽 _𝕣 𝕩: (𝕗 b.Same ceil) ∧ "runs" Is 𝕩 ? 𝕊 0 b.Pick "runs" b.Parts 𝕩 ;
  𝔽 _𝕣 𝕩: (𝕗 b.Same ceil) ∧ "dict" Is 𝕩 ? c‿d ← "dict" b.Parts 𝕩 ⋄ 𝕊 (0 < (≠d) b.Hist c) / d ;
  𝔽 _𝕣 𝕩: (𝕗 b.Same plus) ∧ b.Flat 𝕩 ? b.FoldAdd 𝕩 ;
  𝔽 _𝕣 𝕩: (𝕗 b.Same ceil) ∧ b.Flat 𝕩 ? b.FoldMax 𝕩 ;
  𝔽 _𝕣 𝕩: 𝔽 b._fold b.Deshape 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: "´: 𝕩 must be a list" ! 1==𝕩 ⋄ 𝕨 𝔽 b._fold b.Deshape 𝕩
}

_insert ⇐ {
  𝔽 _𝕣 𝕩: "˝: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ 0=≠𝕩 ? (CellShape 𝕩) ⥊ Identity 𝕗 ;
  𝔽 _𝕣 𝕩: 𝔽 b._fold MajorCells 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: "˝: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ 𝕨 𝔽 b._fold MajorCells 𝕩
}

_scan ⇐ {
  𝔽 _𝕣 𝕩: "`: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ 0=≠𝕩 ? 𝕩 ;
  𝔽 _𝕣 𝕩: (1==𝕩) ∧ (𝕗 b.Same plus) ∧ b.Flat 𝕩 ? b.ScanAdd 𝕩 ;
  𝔽 _𝕣 𝕩: (1==𝕩) ∧ (𝕗 b.Same ceil) ∧ b.Flat 𝕩 ? b.ScanMax 𝕩 ;
  𝔽 _𝕣 𝕩: 1==𝕩 ? 𝔽 b._scan b.Deshape 𝕩 ;
  𝔽 _𝕣 𝕩: > 𝔽 b._scan MajorCells 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: "`: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ 0=≠𝕩 ? 𝕩 ;
  𝕨 𝔽 _𝕣 𝕩: 1==𝕩 ?   # 𝕨 is a 0-cell, so a rank-0 array is unwrapped
    "`: 𝕨 must have the shape of a cell of 𝕩" ! 0==𝕨
    ⟨1, ≠𝕩⟩ b.Slice 𝔽 b._scan b.Cat ⟨⟨⊑𝕨⟩, b.Deshape 𝕩⟩ ;
  𝕨 𝔽 _𝕣 𝕩:
    cells ← MajorCells 𝕩
    > ⟨1, ≠cells⟩ b.Slice 𝔽 b._scan b.Cat ⟨⟨𝕨⟩, cells⟩
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
    (b.Cat ⟨⟨(Ln 𝕨)+Ln 𝕩⟩, Cs 𝕩⟩) b.Reshape b.Cat ⟨Els 𝕨, Els 𝕩⟩
}

Couple ⇐ {𝕊 𝕩: >⟨𝕩⟩ ; 𝕨 𝕊 𝕩: >⟨𝕨, 𝕩⟩}
Pair ⇐ {𝕊 𝕩: ⟨𝕩⟩ ; 𝕨 𝕊 𝕩: ⟨𝕨, 𝕩⟩}

Take ⇐ {
  𝕊 𝕩: "↑: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ (↕1+≠𝕩) 𝕊¨ <𝕩 ;
  𝕨 𝕊 𝕩:
    "↑: only a number 𝕨 is supported" ! 1 b.Eq b.Type 𝕨
    x ← {𝕊 v: 0==v ? ⥊v ; 𝕊 v: v} 𝕩
    n ← ≠x ⋄ m ← |𝕨 ⋄ cs ← CellShape x
    keep ← m⌊n ⋄ pad ← m-keep
    kept ← (((𝕨<0) ⊑ ⟨0, n-keep⟩) + ↕keep) SelCells x
    fill ← (pad × ×´cs) ⥊ < {𝕊 p: 0<p ? b.Fill b.Deshape x ; 𝕊 p: 0} pad
    (b.Cat ⟨⟨m⟩, cs⟩) b.Reshape b.Cat (𝕨<0) ⊑ ⟨⟨kept, fill⟩, ⟨fill, kept⟩⟩
}

Drop ⇐ {
  𝕊 𝕩: "↓: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ (↕1+≠𝕩) 𝕊¨ <𝕩 ;
  𝕨 𝕊 𝕩:
    "↓: only a number 𝕨 is supported" ! 1 b.Eq b.Type 𝕨
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
  𝕨 𝕊 𝕩: (1==𝕨) ∧ "dict" Is 𝕩 ? c‿d ← "dict" b.Parts 𝕩 ⋄ b.MkDict ⟨c, 𝕨 𝕊 d⟩ ;
  𝕨 𝕊 𝕩: (1==𝕨) ∧ "runs" Is 𝕩 ? v‿c ← "runs" b.Parts 𝕩 ⋄ b.MkRuns ⟨𝕨 𝕊 v, c⟩ ;
  𝕨 𝕊 𝕩: (1==𝕨) ∧ "const" Is 𝕩 ? v‿n ← "const" b.Parts 𝕩 ⋄ b.MkConst ⟨0 b.Pick 𝕨 𝕊 ⟨v⟩, n⟩ ;
  𝕨 𝕊 𝕩:
    "⊐: 𝕨 must have rank at least 1" ! 1≤=𝕨
    c ← (=𝕨)-1
    "⊐: 𝕩 must have rank at least that of a cell of 𝕨" ! c ≤ =𝕩
    0=c ? (≢𝕩) b.Reshape (b.Deshape 𝕨) b.IndexOf Els 𝕩 ;
  𝕨 𝕊 𝕩:
    c ← (=𝕨)-1
    fs‿xl ← c KCells 𝕩
    fs b.Reshape (MajorCells 𝕨) b.IndexOf xl
}

Member ⇐ {
  𝕊 𝕩: "∊: 𝕩 must have rank at least 1" ! 1≤=𝕩 ⋄ (𝕩⊐𝕩) = ↕≠𝕩 ;
  𝕨 𝕊 𝕩: (1==𝕩) ∧ "dict" Is 𝕨 ? c‿d ← "dict" b.Parts 𝕨 ⋄ b.MkDict ⟨c, d 𝕊 𝕩⟩ ;
  𝕨 𝕊 𝕩: (1==𝕩) ∧ "runs" Is 𝕨 ? v‿c ← "runs" b.Parts 𝕨 ⋄ b.MkRuns ⟨v 𝕊 𝕩, c⟩ ;
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
    counts ← g b.Hist kk
    ord ← (⍋kk) ⊏ ids
    t ← 𝕩
    ((+`counts)-counts) {((𝕨+↕𝕩)⊏ord) ⊏ t}¨ counts
}

# Effective cell rank of a value with rank 𝕨, for rank number 𝕩
Eff ← {(𝕩≥0) ⊑ ⟨0⌈𝕨+𝕩, 𝕨⌊𝕩⟩}

# A cell of fills with the shape of the r-cells of 𝕩. With an empty frame, ⎉
# applies 𝔽 to one to find the shape of a result cell.
FillCell ← {(⟨(=𝕩)-𝕨, 𝕨⟩ b.Slice ≢𝕩) ⥊ < b.Fill ⥊𝕩}

_rank_ ⇐ {
  𝔽 _𝕣_ 𝔾 𝕩:
    l ← ⥊ 𝔾 𝕩
    c ← (=𝕩) Eff (((≠l)-1) ⊑ 0‿1‿0) ⊑ l
    fs‿cl ← c KCells 𝕩
    0 = ×´fs ? (fs ∾ ≢ 𝔽 c FillCell 𝕩) b.Reshape ⟨⟩ ;
  𝔽 _𝕣_ 𝔾 𝕩:
    l ← ⥊ 𝔾 𝕩
    c ← (=𝕩) Eff (((≠l)-1) ⊑ 0‿1‿0) ⊑ l
    fs‿cl ← c KCells 𝕩
    > fs ⥊ 𝔽 b._each cl ;
  𝕨 𝔽 _𝕣_ 𝔾 𝕩:
    l ← ⥊ 𝕨 𝔾 𝕩
    rw‿rx ← (((≠l)-1) ⊑ ⟨0‿0, 0‿1, 1‿2⟩) ⊏ l
    cw ← (=𝕨) Eff rw ⋄ cx ← (=𝕩) Eff rx
    fw‿wl ← cw KCells 𝕨
    fx‿xl ← cx KCells 𝕩
    fs ← (fw <○≠ fx) ⊑ ⟨fw, fx⟩
    "Mapping: leading axes of the frames must match" ! fw ≡○((fw ⌊○≠ fx)⊸↑) fx
    0 = ×´fs ? (fs ∾ ≢ (cw FillCell 𝕨) 𝔽 cx FillCell 𝕩) b.Reshape ⟨⟩ ;
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
  g 𝕊 v: b.IsMarker g ? ⟨⟨g⟩, ⟨v⟩⟩ ;
  g 𝕊 v: 0 b.Eq b.IsArr g ? "⌾: 𝔽 changed a value that 𝔾 created" ! g ≡ v ⋄ ⟨⟨⟩, ⟨⟩⟩ ;
  g 𝕊 v:
    "⌾: 𝔽 must not change the shape of 𝔾's result" ! (b.IsArr v) ∧ (≢g) ≡ ≢v
    parts ← (Els g) 𝕊¨ Els v
    ⟨b.Cat ⊑¨parts, b.Cat 1⊑¨parts⟩
}
_put ← {   # v 𝔽 _put 𝕩: 𝕩 with the elements in 𝔽 𝕩 replaced by v
  "⌾: only an array 𝕩 is supported" ! b.IsArr 𝕩
  mk ← (≢𝕩) ⥊ b.Markers b.Count 𝕩
  m‿vals ← (𝔽 mk) Walk 𝕨
  (≢𝕩) ⥊ ⟨(b.Deshape mk) b.IndexOf m, vals⟩ b.Scatter Els 𝕩
}
_under_ ⇐ {
  𝔽 _𝕣_ 𝔾 𝕩: (𝔽 𝔾 𝕩) 𝔾 _put 𝕩 ;
  𝕨 𝔽 _𝕣_ 𝔾 𝕩: ((𝔾 𝕨) 𝔽 𝔾 𝕩) 𝔾 _put 𝕩
}
