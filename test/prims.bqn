# test/prims.bqn: differential tests of src/prims.bqn, run on CBQN, against
# CBQN's built-in primitives.
#
#   bqn test/prims.bqn [cases per test] [seed]
#
# The tests and generators are in test/gen.bqn. Outcomes:
#   ok        same result, or both fail
#   MISMATCH  both succeed with different results: a bug
#   gap       only ours fails: something the dialect doesn't support yet
#   lenient   only CBQN fails: ours accepts an invalid argument

Arg ← {𝕨 𝕊 i: i < ≠•args ? •ParseFloat i⊑•args ; 𝕨 𝕊 i: 𝕨}
cases ← 200 Arg 0
g ← (1 Arg 1) •Import "gen.bqn"

d ← •Import "../src/dialect.bqn"
b ← •Import "../src/b.bqn"
n ← ≠g.tests
list ← "testList ⇐ ⟨"∾(1↓∾{",T"∾•Fmt 𝕩}¨ ↕n)∾"⟩"∾@+10
p ← "prims.bqn" d.LoadSrc (•FChars "../src/prims.bqn") ∾ (g.Defs @) ∾ list

args ← g.Cases cases
res ← {𝕊 ours‿src‿as: theirs ← •BQN src ⋄ {⟨g.Try ours‿𝕩, g.Try theirs‿𝕩⟩}¨ as}¨ <˘⍉> p.testList ‿ (1⊑¨g.tests) ‿ args
bad ← args g.Report res
•Out "encoded paths: " ∾ ∾ ´ {" "∾𝕨∾" "∾•Fmt 𝕩}¨´ b.Stats @
•Exit 0 < bad
