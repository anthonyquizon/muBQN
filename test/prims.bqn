# test/prims.bqn: differential tests of the dialect primitives against CBQN.
#
#   bqn test/prims.bqn [cases per test] [seed]
#
# Each test runs one primitive (or derived function) from src/prims.bqn and
# CBQN's built-in on the same random arguments. Outcomes:
#   ok        same result, or both fail
#   MISMATCH  both succeed with different results: a bug
#   gap       only ours fails: something the dialect doesn't support yet
#   lenient   only CBQN fails: ours accepts an invalid argument

p ← (•Import "../src/dialect.bqn").Load "prims.bqn"

Arg ← {𝕨 𝕊 i: i < ≠•args ? •ParseFloat i⊑•args ; 𝕨 𝕊 i: 𝕨}
cases ← 200 Arg 0
rng ← •MakeRand 1 Arg 1
R ← rng.Range

# ---- generators. Each takes @ and returns a value.
Int ← {𝕤 ⋄ ¯3 + R 7}
Num ← {𝕊: 0=R 5 ? 0.5 × ¯6 + R 13 ; 𝕊: Int @}
Shp ← {R¨ 𝕩⥊4}                               # random shape of rank 𝕩
Arr ← {s ← Shp 𝕩 ⋄ s ⥊ Num¨ ↕×´s}            # numbers, rank 𝕩
IArr ← {s ← Shp 𝕩 ⋄ s ⥊ {𝕤 ⋄ R 3}¨ ↕×´s}     # small naturals, many repeats
List ← {𝕤 ⋄ Arr 1}
Nest ← {𝕊 d: d=0 ? Num @ ; 𝕊 d: (R 4) ⥊ {𝕤 ⋄ (R 3) ◶ ⟨Num, List, {𝕤 ⋄ Nest d-1}⟩ @}¨ ↕4}
Any ← {𝕤 ⋄ (R 7) ◶ ⟨Num, {𝕤⋄Arr 0}, List, List, {𝕤⋄Arr 2}, {𝕤⋄Arr 3}, {𝕤⋄Nest 2}⟩ @}
Ranked ← {𝕤 ⋄ Arr 1 + R 3}                    # rank 1 to 3

AgreePair ← {𝕤   # arguments whose shapes agree on leading axes
  s ← Shp R 4 ⋄ t ← (R 1+≠s) ↑ s
  a ← s ⥊ Num¨ ↕×´s ⋄ b ← t ⥊ Num¨ ↕×´t
  b ↩ (0=≠t) ◶ ⟨⊢, {(R 2) ⊑ ⟨𝕩, ⊑𝕩⟩}⟩ b    # sometimes an atom
  (R 2) ⊑ ⟨⟨a, b⟩, ⟨b, a⟩⟩
}
Arith2 ← {𝕤 ⋄ (R 4) ◶ ⟨AgreePair, AgreePair, {𝕤⋄⟨Num@, Num@⟩}, {𝕤⋄(R 2)⊑⟨⟨Nest 2, Num@⟩, ⟨Num@, Nest 2⟩⟩}⟩ @}
Arith1 ← {𝕤 ⋄ ⟨(R 3) ◶ ⟨Num, {𝕤⋄Arr R 3}, {𝕤⋄Nest 2}⟩ @⟩}

M ← {𝕤 ⋄ ⟨Any @⟩}                             # one argument of any kind
Pairs ← {𝕤 ⋄ (R 3) ◶ ⟨{𝕤⋄⟨Any@, Any@⟩}, {𝕤⋄a←Any@ ⋄ ⟨a,a⟩}, AgreePair⟩ @}
IdxFor ← {𝕤   # 𝕨⊏𝕩 with some indices out of range
  x ← Ranked @ ⋄ n ← ≠x ⋄ s ← Shp R 3
  ⟨s ⥊ {𝕤 ⋄ (-n+1) + R 2+2×n}¨ ↕×´s, x⟩
}
PickFor ← {𝕤
  x ← Arr R 3
  I ← {𝕤 ⋄ {(-1+𝕩) + R 2×𝕩+1}⍟(0<⊢)¨ ≢x}
  (R 3) ◶ ⟨{𝕤⋄⟨Int@, List@⟩}, {𝕤⋄⟨I@, x⟩}, {𝕤⋄⟨⟨I@, I@⟩, x⟩}⟩ @
}
MergeArg ← {𝕤 ⋄ s ← Shp R 3 ⋄ c ← Shp R 3 ⋄ ⟨s ⥊ {𝕤 ⋄ c ⥊ Num¨ ↕×´c}¨ ↕×´s⟩}
RepArg ← {𝕤
  x ← Arr 1 + R 2
  ⟨(R 3) ◶ ⟨{𝕤⋄R 3}, {𝕤⋄{𝕤⋄R 3}¨ ↕≠x}, {𝕤⋄{𝕤⋄R 2}¨ ↕≠x}⟩ @, x⟩
}
ScanD ← {𝕤 ⋄ x ← Arr 1 + R 2 ⋄ ⟨(1↓≢x) ⥊ Num¨ ↕×´1↓≢x, x⟩}
JoinArg ← {𝕤
  (R 5) ◶ ⟨
    {𝕤⋄⟨List@, List@⟩}, {𝕤⋄⟨Num@, List@⟩}, {𝕤⋄⟨Num@, Num@⟩}
    {𝕤⋄c←R 3 ⋄ ⟨((R 3)‿c)⥊1, ((R 3)‿c)⥊2⟩}
    {𝕤⋄c←R 3 ⋄ ⟨((R 3)‿c)⥊1, c⥊2⟩}
  ⟩ @
}
TakeArg ← {𝕤 ⋄ ⟨¯5 + R 11, (R 3) ◶ ⟨Num, List, {𝕤⋄Arr 2}⟩ @⟩}
SearchArg ← {𝕤 ⋄ (R 2) ◶ ⟨{𝕤⋄⟨IArr 1, IArr R 3⟩}, {𝕤⋄c←1+R 2 ⋄ ⟨(⟨R 4, c⟩)⥊{𝕤⋄R 2}¨↕8, (⟨R 3, c⟩)⥊{𝕤⋄R 2}¨↕6⟩}⟩ @}
FindArg ← {𝕤 ⋄ ⟨{𝕤⋄R 2}¨ ↕R 3, {𝕤⋄R 2}¨ ↕R 7⟩}
GroupArg ← {𝕤
  x ← Arr 1 + R 2 ⋄ n ← ≠x
  ⟨{𝕤 ⋄ ¯1 + R 4}¨ ↕n + R 2, x⟩
}
Keys ← {𝕤 ⋄ ⟨{𝕤 ⋄ ¯1 + R 4}¨ ↕R 7⟩}
RankArg ← {𝕤 ⋄ ⟨Arr R 4⟩}
Rank2 ← {𝕤 ⋄ AgreePair @}

# ---- tests: name, ours, CBQN's, generator
tests ← ⟨
  ⟨"≢𝕩",   p.Shape,   ≢, M⟩,         ⟨"𝕨≢𝕩",  p.Shape,   ≢, Pairs⟩
  ⟨"≡𝕩",   p.Match,   ≡, M⟩,         ⟨"𝕨≡𝕩",  p.Match,   ≡, Pairs⟩
  ⟨"⥊𝕩",   p.Reshape, ⥊, M⟩
  ⟨"𝕨⥊𝕩",  p.Reshape, ⥊, {𝕤 ⋄ ⟨(R 2) ◶ ⟨{𝕤⋄R 5}, {𝕤⋄Shp R 3}⟩ @, Any@⟩}⟩
  ⟨"⊏𝕩",   p.Select,  ⊏, {𝕤 ⋄ ⟨Ranked@⟩}⟩, ⟨"𝕨⊏𝕩",  p.Select,  ⊏, IdxFor⟩
  ⟨"⊑𝕩",   p.Pick,    ⊑, M⟩,         ⟨"𝕨⊑𝕩",  p.Pick,    ⊑, PickFor⟩
  ⟨"↕𝕩",   p.Range,   ↕, {𝕤 ⋄ ⟨(R 2) ◶ ⟨{𝕤⋄R 5}, {𝕤⋄Shp R 3}⟩ @⟩}⟩
  ⟨"-¨𝕩",  p.Minus p._each, -¨, Arith1⟩
  ⟨"𝕨+¨𝕩", p.Plus p._each,  +¨, AgreePair⟩
  ⟨"𝕨⋈⌜𝕩", p.Pair p._table, ⋈⌜, {𝕤 ⋄ ⟨Any@, Any@⟩}⟩
  ⟨"⍋𝕩",   p.GradeUp, ⍋, {𝕤 ⋄ ⟨IArr 1 + R 2⟩}⟩
  ⟨"⍒𝕩",   p.GradeDown, ⍒, {𝕤 ⋄ ⟨IArr 1⟩}⟩
  ⟨"⌽𝕩",   p.Reverse, ⌽, {𝕤 ⋄ ⟨Ranked@⟩}⟩, ⟨"𝕨⌽𝕩",  p.Reverse, ⌽, {𝕤 ⋄ ⟨¯4 + R 9, Ranked@⟩}⟩
  ⟨"+𝕩",   p.Plus,    +, Arith1⟩,    ⟨"𝕨+𝕩",  p.Plus,    +, Arith2⟩
  ⟨"-𝕩",   p.Minus,   -, Arith1⟩,    ⟨"𝕨-𝕩",  p.Minus,   -, Arith2⟩
  ⟨"×𝕩",   p.Times,   ×, Arith1⟩,    ⟨"𝕨×𝕩",  p.Times,   ×, Arith2⟩
  ⟨"÷𝕩",   p.Divide,  ÷, Arith1⟩,    ⟨"𝕨÷𝕩",  p.Divide,  ÷, Arith2⟩
  ⟨"⌊𝕩",   p.Floor,   ⌊, Arith1⟩,    ⟨"𝕨⌊𝕩",  p.Floor,   ⌊, Arith2⟩
  ⟨"⌈𝕩",   p.Ceil,    ⌈, Arith1⟩,    ⟨"𝕨⌈𝕩",  p.Ceil,    ⌈, Arith2⟩
  ⟨"|𝕩",   p.Abs,     |, Arith1⟩,    ⟨"𝕨|𝕩",  p.Abs,     |, Arith2⟩
  ⟨"¬𝕩",   p.Not,     ¬, Arith1⟩,    ⟨"𝕨¬𝕩",  p.Not,     ¬, Arith2⟩
  ⟨"=𝕩",   p.Equal,   =, M⟩,         ⟨"𝕨=𝕩",  p.Equal,   =, Arith2⟩
  ⟨"≠𝕩",   p.NotEq,   ≠, M⟩,         ⟨"𝕨≠𝕩",  p.NotEq,   ≠, Arith2⟩
  ⟨"<𝕩",   p.Less,    <, M⟩,         ⟨"𝕨<𝕩",  p.Less,    <, Arith2⟩
  ⟨">𝕩",   p.Greater, >, MergeArg⟩,  ⟨"𝕨>𝕩",  p.Greater, >, Arith2⟩
  ⟨"𝕨≤𝕩",  p.LessEq,  ≤, Arith2⟩,    ⟨"𝕨≥𝕩",  p.GreaterEq, ≥, Arith2⟩
  ⟨"∧𝕩",   p.And,     ∧, {𝕤 ⋄ ⟨IArr 1 + R 2⟩}⟩, ⟨"𝕨∧𝕩",  p.And, ∧, Arith2⟩
  ⟨"∨𝕩",   p.Or,      ∨, {𝕤 ⋄ ⟨IArr 1⟩}⟩,  ⟨"𝕨∨𝕩",  p.Or,  ∨, Arith2⟩
  ⟨"/𝕩",   p.Replicate, /, {𝕤 ⋄ ⟨IArr 1⟩}⟩, ⟨"𝕨/𝕩", p.Replicate, /, RepArg⟩
  ⟨"+´𝕩",  p.Plus p._fold,  +´, {𝕤 ⋄ ⟨List@⟩}⟩
  ⟨"-´𝕩",  p.Minus p._fold, -´, {𝕤 ⋄ ⟨List@⟩}⟩
  ⟨"⌈´𝕩",  p.Ceil p._fold,  ⌈´, {𝕤 ⋄ ⟨List@⟩}⟩
  ⟨"𝕨-´𝕩", p.Minus p._fold, -´, {𝕤 ⋄ ⟨Num@, List@⟩}⟩
  ⟨"∾´𝕩",  p.Join p._fold,  ∾´, {𝕤 ⋄ ⟨List¨ ↕R 4⟩}⟩
  ⟨"+˝𝕩",  p.Plus p._insert, +˝, {𝕤 ⋄ ⟨Arr 1 + R 2⟩}⟩
  ⟨"+`𝕩",  p.Plus p._scan,   +`, {𝕤 ⋄ ⟨Arr 1 + R 2⟩}⟩
  ⟨"-`𝕩",  p.Minus p._scan,  -`, {𝕤 ⋄ ⟨Arr 1 + R 2⟩}⟩
  ⟨"⌈`𝕩",  p.Ceil p._scan,   ⌈`, {𝕤 ⋄ ⟨Arr 1⟩}⟩
  ⟨"𝕨-`𝕩", p.Minus p._scan,  -`, ScanD⟩
  ⟨"∾𝕩",   p.Join, ∾, {𝕤 ⋄ ⟨List¨ ↕1 + R 3⟩}⟩, ⟨"𝕨∾𝕩",  p.Join, ∾, JoinArg⟩
  ⟨"≍𝕩",   p.Couple, ≍, M⟩, ⟨"𝕨≍𝕩",  p.Couple, ≍, {𝕤 ⋄ a←Any@ ⋄ ⟨a, (R 2) ◶ ⟨{𝕤⋄a}, Any⟩ @⟩}⟩
  ⟨"⋈𝕩",   p.Pair, ⋈, M⟩,  ⟨"𝕨⋈𝕩",  p.Pair, ⋈, Pairs⟩
  ⟨"↑𝕩",   p.Take, ↑, {𝕤 ⋄ ⟨Ranked@⟩}⟩, ⟨"𝕨↑𝕩", p.Take, ↑, TakeArg⟩
  ⟨"↓𝕩",   p.Drop, ↓, {𝕤 ⋄ ⟨Ranked@⟩}⟩, ⟨"𝕨↓𝕩", p.Drop, ↓, TakeArg⟩
  ⟨"⊐𝕩",   p.IndexOf, ⊐, {𝕤 ⋄ ⟨IArr 1 + R 2⟩}⟩, ⟨"𝕨⊐𝕩", p.IndexOf, ⊐, SearchArg⟩
  ⟨"∊𝕩",   p.Member, ∊, {𝕤 ⋄ ⟨IArr 1 + R 2⟩}⟩,  ⟨"𝕨∊𝕩", p.Member, ∊, {𝕤 ⋄ ⌽SearchArg@}⟩
  ⟨"⍷𝕩",   p.Find, ⍷, {𝕤 ⋄ ⟨IArr 1 + R 2⟩}⟩,  ⟨"𝕨⍷𝕩", p.Find, ⍷, FindArg⟩
  ⟨"⊔𝕩",   p.Group, ⊔, Keys⟩, ⟨"𝕨⊔𝕩", p.Group, ⊔, GroupArg⟩
  ⟨"+´⎉1 𝕩", p.Plus p._fold p._rank_ 1, +´⎉1, RankArg⟩
  ⟨"≢⎉0 𝕩",  p.Shape p._rank_ 0, ≢⎉0, RankArg⟩
  ⟨"⌽⎉¯1 𝕩", p.Reverse p._rank_ ¯1, ⌽⎉¯1, {𝕤 ⋄ ⟨Arr 2 + R 2⟩}⟩
  ⟨"𝕨+⎉1 𝕩", p.Plus p._rank_ 1, +⎉1, Rank2⟩
  ⟨"𝕨⋈⎉0‿1 𝕩", p.Pair p._rank_ 0‿1, ⋈⎉0‿1, Rank2⟩
  ⟨"⌽˘𝕩",    p.Reverse p._cells, ⌽˘, {𝕤 ⋄ ⟨Arr 2 + R 2⟩}⟩
  ⟨"-⌾⌽𝕩",   p.Minus p._under_ p.Reverse, -⌾⌽, {𝕤 ⋄ ⟨Ranked@⟩}⟩
  ⟨"-⌾(1⊸⊏)𝕩", p.Minus p._under_ (1⊸p.Select), -⌾(1⊸⊏), {𝕤 ⋄ ⟨Ranked@⟩}⟩
  ⟨"⋈⌾⊑𝕩",   p.Pair p._under_ p.Pick, ⋈⌾⊑, {𝕤 ⋄ ⟨Ranked@⟩}⟩
  ⟨"⌽⌾(2⊸↑)𝕩", p.Reverse p._under_ (2⊸p.Take), ⌽⌾(2⊸↑), {𝕤 ⋄ ⟨Ranked@⟩}⟩
  ⟨"𝕨+⌾(1⊸↓)𝕩", p.Plus p._under_ (1⊸p.Drop), +⌾(1⊸↓), {𝕤 ⋄ x←List@ ⋄ ⟨(0⌈¯1+≠x)⥊1, x⟩}⟩
  ⟨"-⌾(1⊸+)𝕩", p.Minus p._under_ (1⊸p.Plus), -⌾(1⊸+), {𝕤 ⋄ ⟨List@⟩}⟩
⟩

# ---- running
Run ← {𝕊 f‿a: 1=≠a ? F ⊑a ; 𝕊 f‿a: (⊑a) F 1⊑a}
Try ← {⟨1, Run 𝕩⟩}⎊{𝕊: ⟨0, •CurrentError @⟩}
# CBQN's ≡ finds arrays holding NaN unequal to themselves; compare text then
Same ← {(𝕨≡𝕩) ∨ (•Repr⎊•Fmt 𝕨) ≡ •Repr⎊•Fmt 𝕩}
Outcome ← {
  𝕊 ⟨o,x⟩‿⟨c,y⟩: o∧c ? (x Same y) ⊑ "MISMATCH"‿"ok" ;
  𝕊 ⟨o,x⟩‿⟨c,y⟩: o ? "lenient" ;
  𝕊 ⟨o,x⟩‿⟨c,y⟩: c ? "gap" ;
  𝕊 z: "ok"
}
kinds ← "ok"‿"MISMATCH"‿"gap"‿"lenient"

Short ← {60<≠𝕩 ? (57↑𝕩)∾"..." ; 𝕩}
Fmt ← Short •Fmt
Arglist ← {1=≠𝕩 ? Fmt ⊑𝕩 ; (Fmt ⊑𝕩)∾"  ,  "∾Fmt 1⊑𝕩}
Example ← {𝕊 kind‿a‿⟨o,x⟩‿⟨c,y⟩:
  "      "∾(Arglist a)∾"  →  "∾{
    kind≡"gap" ? Short x ;
    kind≡"lenient" ? "ours "∾(Fmt x)∾", CBQN: "∾Short y ;
    "ours "∾(Fmt x)∾", CBQN "∾Fmt y
  }
}

total ← 0‿0‿0‿0
{𝕊 name‿ours‿theirs‿gen:
  rs ← {𝕤 ⋄ a ← Gen @ ⋄ o ← Try ours‿a ⋄ c ← Try theirs‿a ⋄ ⟨Outcome o‿c, a, o, c⟩}¨ ↕cases
  ks ← ⊑¨rs
  n ← kinds {+´ (<𝕨) ≡¨ 𝕩}¨ <ks
  total +↩ n
  •Out (14↑name) ∾ ∾ (0<n) / n {"  "∾(•Fmt 𝕨)∾" "∾𝕩}¨ kinds
  {𝕊 kind: •Out∘Example¨ (2⌊≠)⊸↑ (ks ≡¨ <kind) / rs}¨ 1↓kinds
}¨ tests
•Out ""
•Out "total" ∾ ∾ total {"  "∾(•Fmt 𝕨)∾" "∾𝕩}¨ kinds
•Exit 0 < 1⊑total
