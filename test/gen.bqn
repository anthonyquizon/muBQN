# test/gen.bqn: random arguments, the list of tests, and reporting, shared by
# test/prims.bqn (the dialect run on CBQN) and test/emit.bqn (compiled C).
#
#   g ← seed •Import "gen.bqn"
#
# A test is ⟨name, source, generator⟩. The source is BQN for a function, such
# as "+´" or "-⌾(1⊸⊏)": CBQN's version is •BQN source, and the dialect's is
# the same source compiled against src/prims.bqn (see Defs).

rng ← •MakeRand •args
R ← rng.Range

# ---- generators. Each takes @ and returns a value.
Int ← {𝕤 ⋄ ¯3 + R 7}
Num ← {𝕊: 0=R 5 ? 0.5 × ¯6 + R 13 ; 𝕊: Int @}
Shp ← {R¨ 𝕩⥊4}                               # random shape of rank 𝕩
Arr ← {s ← Shp 𝕩 ⋄ s ⥊ Num¨ ↕×´s}            # numbers, rank 𝕩
IArr ← {s ← Shp 𝕩 ⋄ s ⥊ {𝕤 ⋄ R 3}¨ ↕×´s}     # small naturals, many repeats
# Lists with structure, so the shim can claim encodings for them
Struct ← {𝕤
  n ← R 8
  (R 6) ◶ ⟨
    {𝕤 ⋄ n ⥊ Num@}                          # constant
    {𝕤 ⋄ (Int@) + (Int@) × ↕n}              # range
    {𝕤 ⋄ (R¨ n⥊4) / Num¨ ↕n}                # runs
    {𝕤 ⋄ (R¨ n⥊3) ⊏ Num¨ ↕3}                # few distinct values
    {𝕤 ⋄ n ⥊ 0.1}                           # +´ must not use n×v here
    {𝕤 ⋄ ∧ (R¨ n⥊4) / Num¨ ↕n}              # sorted
  ⟩ @
}
List ← {𝕤 ⋄ (R 2) ◶ ⟨{𝕤 ⋄ Arr 1}, Struct⟩ @}
Nest ← {𝕊 d: d=0 ? Num @ ; 𝕊 d: (R 4) ⥊ {𝕤 ⋄ (R 3) ◶ ⟨Num, List, {𝕤 ⋄ Nest d-1}⟩ @}¨ ↕4}
Any ← {𝕤 ⋄ (R 7) ◶ ⟨Num, {𝕤⋄Arr 0}, List, List, {𝕤⋄Arr 2}, {𝕤⋄Arr 3}, {𝕤⋄Nest 2}⟩ @}
Ranked ← {𝕤 ⋄ Arr 1 + R 3}                    # rank 1 to 3

AgreePair ← {𝕤   # arguments whose shapes agree on leading axes
  s ← Shp R 4 ⋄ t ← (R 1+≠s) ↑ s
  a ← s ⥊ Num¨ ↕×´s ⋄ b ← t ⥊ Num¨ ↕×´t
  b ↩ (0=≠t) ◶ ⟨⊢, {(R 2) ⊑ ⟨𝕩, ⊑𝕩⟩}⟩ b    # sometimes an atom
  (R 2) ⊑ ⟨⟨a, b⟩, ⟨b, a⟩⟩
}
Arith2 ← {𝕤 ⋄ (R 5) ◶ ⟨AgreePair, AgreePair, {𝕤⋄⟨Num@, Num@⟩}, {𝕤⋄(R 2)⊑⟨⟨Nest 2, Num@⟩, ⟨Num@, Nest 2⟩⟩}, {𝕤⋄(R 2)⊑⟨⟨Int@, Struct@⟩, ⟨Struct@, Int@⟩⟩}⟩ @}
Arith1 ← {𝕤 ⋄ ⟨(R 4) ◶ ⟨Num, {𝕤⋄Arr R 3}, {𝕤⋄Nest 2}, Struct⟩ @⟩}

M ← {𝕤 ⋄ ⟨Any @⟩}                             # one argument of any kind
Pairs ← {𝕤 ⋄ (R 3) ◶ ⟨{𝕤⋄⟨Any@, Any@⟩}, {𝕤⋄a←Any@ ⋄ ⟨a,a⟩}, AgreePair⟩ @}
IdxFor ← {𝕤   # 𝕨⊏𝕩 with some indices out of range, and some ranges
  x ← (R 2) ◶ ⟨Ranked, Struct⟩ @ ⋄ n ← ≠x ⋄ s ← Shp R 3
  i ← s ⥊ {𝕤 ⋄ (-n+1) + R 2+2×n}¨ ↕×´s
  ⟨(R 3) ◶ ⟨{𝕤⋄i}, {𝕤⋄i}, {𝕤⋄(R 1+n) + ↕R 1+n}⟩ @, x⟩
}
PickFor ← {𝕤
  x ← Arr R 3
  I ← {𝕤 ⋄ {(-1+𝕩) + R 2×𝕩+1}⍟(0<⊢)¨ ≢x}
  (R 3) ◶ ⟨{𝕤⋄⟨Int@, List@⟩}, {𝕤⋄⟨I@, x⟩}, {𝕤⋄⟨⟨I@, I@⟩, x⟩}⟩ @
}
MergeArg ← {𝕤 ⋄ s ← Shp R 3 ⋄ c ← Shp R 3 ⋄ ⟨s ⥊ {𝕤 ⋄ c ⥊ Num¨ ↕×´c}¨ ↕×´s⟩}
RepArg ← {𝕤
  x ← (R 2) ◶ ⟨{𝕤⋄Arr 1 + R 2}, Struct⟩ @
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
SearchArg ← {𝕤 ⋄ (R 3) ◶ ⟨{𝕤⋄⟨IArr 1, IArr R 3⟩}, {𝕤⋄c←1+R 2 ⋄ ⟨(⟨R 4, c⟩)⥊{𝕤⋄R 2}¨↕8, (⟨R 3, c⟩)⥊{𝕤⋄R 2}¨↕6⟩}, {𝕤⋄⟨Struct@, Struct@⟩}⟩ @}
Counts ← {𝕤 ⋄ ⟨(R 2) ◶ ⟨{𝕤⋄IArr 1}, {𝕤⋄{𝕤⋄R 5}¨ ↕R 6}⟩ @⟩}
FindArg ← {𝕤 ⋄ ⟨{𝕤⋄R 2}¨ ↕R 3, {𝕤⋄R 2}¨ ↕R 7⟩}
GroupArg ← {𝕤
  x ← Arr 1 + R 2 ⋄ n ← ≠x
  ⟨{𝕤 ⋄ ¯1 + R 4}¨ ↕n + R 2, x⟩
}
Keys ← {𝕤 ⋄ ⟨{𝕤 ⋄ ¯1 + R 4}¨ ↕R 7⟩}
RankArg ← {𝕤 ⋄ ⟨Arr R 4⟩}
Rank2 ← {𝕤 ⋄ AgreePair @}
Sorts ← {𝕤 ⋄ ⟨(R 2) ◶ ⟨{𝕤⋄IArr 1 + R 2}, Struct⟩ @⟩}

# ---- tests: name, source, generator
tests ⇐ ⟨
  ⟨"≢𝕩", "≢", M⟩, ⟨"𝕨≢𝕩", "≢", Pairs⟩
  ⟨"≡𝕩", "≡", M⟩, ⟨"𝕨≡𝕩", "≡", Pairs⟩
  ⟨"⥊𝕩", "⥊", M⟩
  ⟨"𝕨⥊𝕩", "⥊", {𝕤 ⋄ ⟨(R 2) ◶ ⟨{𝕤⋄R 5}, {𝕤⋄Shp R 3}⟩ @, Any@⟩}⟩
  ⟨"⊏𝕩", "⊏", {𝕤 ⋄ ⟨Ranked@⟩}⟩, ⟨"𝕨⊏𝕩", "⊏", IdxFor⟩
  ⟨"⊑𝕩", "⊑", M⟩, ⟨"𝕨⊑𝕩", "⊑", PickFor⟩
  ⟨"↕⊸+𝕩", "↕⊸+", {𝕤 ⋄ ⟨R 6⟩}⟩
  ⟨"↕𝕩", "↕", {𝕤 ⋄ ⟨(R 2) ◶ ⟨{𝕤⋄R 5}, {𝕤⋄Shp R 3}⟩ @⟩}⟩
  ⟨"-¨𝕩", "-¨", Arith1⟩
  ⟨"𝕨+¨𝕩", "+¨", AgreePair⟩
  ⟨"𝕨⋈⌜𝕩", "⋈⌜", {𝕤 ⋄ ⟨Any@, Any@⟩}⟩
  ⟨"⍋𝕩", "⍋", Sorts⟩
  ⟨"⍒𝕩", "⍒", {𝕤 ⋄ ⟨IArr 1⟩}⟩
  ⟨"⌽𝕩", "⌽", {𝕤 ⋄ ⟨(R 2) ◶ ⟨Ranked, Struct⟩ @⟩}⟩, ⟨"𝕨⌽𝕩", "⌽", {𝕤 ⋄ ⟨¯4 + R 9, Ranked@⟩}⟩
  ⟨"+𝕩", "+", Arith1⟩, ⟨"𝕨+𝕩", "+", Arith2⟩
  ⟨"-𝕩", "-", Arith1⟩, ⟨"𝕨-𝕩", "-", Arith2⟩
  ⟨"×𝕩", "×", Arith1⟩, ⟨"𝕨×𝕩", "×", Arith2⟩
  ⟨"÷𝕩", "÷", Arith1⟩, ⟨"𝕨÷𝕩", "÷", Arith2⟩
  ⟨"⌊𝕩", "⌊", Arith1⟩, ⟨"𝕨⌊𝕩", "⌊", Arith2⟩
  ⟨"⌈𝕩", "⌈", Arith1⟩, ⟨"𝕨⌈𝕩", "⌈", Arith2⟩
  ⟨"|𝕩", "|", Arith1⟩, ⟨"𝕨|𝕩", "|", Arith2⟩
  ⟨"¬𝕩", "¬", Arith1⟩, ⟨"𝕨¬𝕩", "¬", Arith2⟩
  ⟨"=𝕩", "=", M⟩, ⟨"𝕨=𝕩", "=", Arith2⟩
  ⟨"≠𝕩", "≠", M⟩, ⟨"𝕨≠𝕩", "≠", Arith2⟩
  ⟨"<𝕩", "<", M⟩, ⟨"𝕨<𝕩", "<", Arith2⟩
  ⟨">𝕩", ">", MergeArg⟩, ⟨"𝕨>𝕩", ">", Arith2⟩
  ⟨"𝕨≤𝕩", "≤", Arith2⟩, ⟨"𝕨≥𝕩", "≥", Arith2⟩
  ⟨"∧𝕩", "∧", Sorts⟩, ⟨"𝕨∧𝕩", "∧", Arith2⟩
  ⟨"∨𝕩", "∨", {𝕤 ⋄ ⟨IArr 1⟩}⟩, ⟨"𝕨∨𝕩", "∨", Arith2⟩
  ⟨"/𝕩", "/", Counts⟩, ⟨"𝕨/𝕩", "/", RepArg⟩
  ⟨"+´𝕩", "+´", {𝕤 ⋄ ⟨List@⟩}⟩
  ⟨"-´𝕩", "-´", {𝕤 ⋄ ⟨List@⟩}⟩
  ⟨"⌈´𝕩", "⌈´", {𝕤 ⋄ ⟨List@⟩}⟩
  ⟨"𝕨-´𝕩", "-´", {𝕤 ⋄ ⟨Num@, List@⟩}⟩
  ⟨"∾´𝕩", "∾´", {𝕤 ⋄ ⟨List¨ ↕R 4⟩}⟩
  ⟨"+˝𝕩", "+˝", {𝕤 ⋄ ⟨Arr 1 + R 2⟩}⟩
  ⟨"+`𝕩", "+`", {𝕤 ⋄ ⟨Arr 1 + R 2⟩}⟩
  ⟨"-`𝕩", "-`", {𝕤 ⋄ ⟨Arr 1 + R 2⟩}⟩
  ⟨"⌈`𝕩", "⌈`", {𝕤 ⋄ ⟨Arr 1⟩}⟩
  ⟨"𝕨-`𝕩", "-`", ScanD⟩
  ⟨"∾𝕩", "∾", {𝕤 ⋄ ⟨List¨ ↕1 + R 3⟩}⟩, ⟨"𝕨∾𝕩", "∾", JoinArg⟩
  ⟨"≍𝕩", "≍", M⟩, ⟨"𝕨≍𝕩", "≍", {𝕤 ⋄ a←Any@ ⋄ ⟨a, (R 2) ◶ ⟨{𝕤⋄a}, Any⟩ @⟩}⟩
  ⟨"⋈𝕩", "⋈", M⟩, ⟨"𝕨⋈𝕩", "⋈", Pairs⟩
  ⟨"↑𝕩", "↑", {𝕤 ⋄ ⟨Ranked@⟩}⟩, ⟨"𝕨↑𝕩", "↑", TakeArg⟩
  ⟨"↓𝕩", "↓", {𝕤 ⋄ ⟨Ranked@⟩}⟩, ⟨"𝕨↓𝕩", "↓", TakeArg⟩
  ⟨"⊐𝕩", "⊐", {𝕤 ⋄ ⟨IArr 1 + R 2⟩}⟩, ⟨"𝕨⊐𝕩", "⊐", SearchArg⟩
  ⟨"∊𝕩", "∊", {𝕤 ⋄ ⟨IArr 1 + R 2⟩}⟩, ⟨"𝕨∊𝕩", "∊", {𝕤 ⋄ ⌽SearchArg@}⟩
  ⟨"⍷𝕩", "⍷", {𝕤 ⋄ ⟨IArr 1 + R 2⟩}⟩, ⟨"𝕨⍷𝕩", "⍷", FindArg⟩
  ⟨"⊔𝕩", "⊔", Keys⟩, ⟨"𝕨⊔𝕩", "⊔", GroupArg⟩
  ⟨"+´⎉1 𝕩", "+´⎉1", RankArg⟩
  ⟨"≢⎉0 𝕩", "≢⎉0", RankArg⟩
  ⟨"⌽⎉¯1 𝕩", "⌽⎉¯1", {𝕤 ⋄ ⟨Arr 2 + R 2⟩}⟩
  ⟨"𝕨+⎉1 𝕩", "+⎉1", Rank2⟩
  ⟨"𝕨⋈⎉0‿1 𝕩", "⋈⎉0‿1", Rank2⟩
  ⟨"⌽˘𝕩", "⌽˘", {𝕤 ⋄ ⟨Arr 2 + R 2⟩}⟩
  ⟨"-⌾⌽𝕩", "-⌾⌽", {𝕤 ⋄ ⟨Ranked@⟩}⟩
  ⟨"-⌾(1⊸⊏)𝕩", "-⌾(1⊸⊏)", {𝕤 ⋄ ⟨Ranked@⟩}⟩
  ⟨"⋈⌾⊑𝕩", "⋈⌾⊑", {𝕤 ⋄ ⟨Ranked@⟩}⟩
  ⟨"⌽⌾(2⊸↑)𝕩", "⌽⌾(2⊸↑)", {𝕤 ⋄ ⟨Ranked@⟩}⟩
  ⟨"𝕨+⌾(1⊸↓)𝕩", "+⌾(1⊸↓)", {𝕤 ⋄ x←List@ ⋄ ⟨(0⌈¯1+≠x)⥊1, x⟩}⟩
  ⟨"-⌾(1⊸+)𝕩", "-⌾(1⊸+)", {𝕤 ⋄ ⟨List@⟩}⟩
⟩

# Dialect definitions of the tests, to append to src/prims.bqn: test i is
# T<i>, and testList lists them all.
Defs ⇐ {𝕤
  D ← {"T"∾(•Fmt 𝕨)∾" ⇐ {𝕊 𝕩: ("∾𝕩∾") 𝕩 ; 𝕨 𝕊 𝕩: 𝕨 ("∾𝕩∾") 𝕩}"∾@+10}
  (@+10) ∾ ∾ (↕≠tests) D¨ 1⊑¨tests
}

# ---- wire format of the C harnesses (src/vm.c PRIM_TEST, test/hand_main.c)
FmtN ← {𝕩≠𝕩 ? "nan" ; 𝕩=∞ ? "inf" ; 𝕩=-∞ ? "-inf" ; {𝕩='¯' ? '-' ; 𝕩}¨ •Repr 𝕩}
Ser ⇐ {
  𝕊 v: 1=•Type v ? "n"∾FmtN v ;
  𝕊 v: 2=•Type v ? "c"∾•Fmt v-@ ;
  𝕊 v: 0=•Type v ? "a "∾(•Fmt =v)∾(∾' '⊸∾¨•Fmt¨≢v)∾∾(' '∾Ser)¨⥊v ;
  𝕊 v: "can't serialize this value" ! 0
}
ParseN ← {𝕩≡"nan" ? 0÷0 ; 𝕩≡"inf" ? ∞ ; 𝕩≡"-inf" ? -∞ ; •ParseFloat 𝕩}
De ← {   # one value from a line of tokens
  ts ← 1↓¨ (¯1++`' '=s) ⊔ s ← ' '∾𝕩 ⋄ i ← 0
  Next ← {𝕤 ⋄ i +↩ 1 ⋄ (i-1)⊑ts}
  P ← {𝕤
    t ← Next@
    {
      'n' = ⊑t ? ParseN 1↓t ;
      'c' = ⊑t ? @ + •ParseFloat 1↓t ;
      'a' = ⊑t ? r ← •ParseFloat Next@ ⋄ s ← {𝕤 ⋄ •ParseFloat Next@}¨ ↕r ⋄ s ⥊ P¨ ↕×´s ;
      ⟨"unknown", t⟩
    }
  }
  P @
}
Result ⇐ {   # a line of output → ⟨1, value⟩ or ⟨0, message⟩
  "ok " ≡ 3↑𝕩 ? ⟨1, De 3↓𝕩⟩ ;
  "err " ≡ 4↑𝕩 ? ⟨0, 4↓𝕩⟩ ;
  ⟨0, "harness: "∾𝕩⟩
}

# ---- running and reporting
Run ⇐ {𝕊 f‿a: 1=≠a ? F ⊑a ; 𝕊 f‿a: (⊑a) F 1⊑a}
Try ⇐ {⟨1, Run 𝕩⟩}⎊{𝕊: ⟨0, •CurrentError @⟩}
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

# Cases n: n argument lists for each test
Cases ⇐ {n ← 𝕩 ⋄ {𝕊 name‿src‿gen: Gen¨ n⥊@}¨ tests}

# results Report args: prints a line per test (and examples of failures),
# then the totals; returns the number of mismatches. results holds, per
# test and case, ⟨ours, theirs⟩ as Try returns them.
# ReportFor is Report over a subset ts of the tests.
Report ⇐ {tests ReportFor 𝕨‿𝕩}
ReportFor ⇐ {ts 𝕊 args‿results:
  total ← 0‿0‿0‿0
  {𝕊 ⟨name, src, gen⟩‿args‿res:
    rs ← args {⟨Outcome 𝕩, 𝕨⟩ ∾ 𝕩}¨ res
    ks ← ⊑¨rs
    n ← kinds {+´ (<𝕨) ≡¨ 𝕩}¨ <ks
    total +↩ n
    •Out (14↑name) ∾ ∾ (0<n) / n {"  "∾(•Fmt 𝕨)∾" "∾𝕩}¨ kinds
    {𝕊 kind: •Out∘Example¨ (2⌊≠)⊸↑ (ks ≡¨ <kind) / rs}¨ 1↓kinds
  }¨ <˘⍉> ts‿args‿results
  •Out ""
  •Out "total" ∾ ∾ total {"  "∾(•Fmt 𝕨)∾" "∾𝕩}¨ kinds
  1⊑total
}
