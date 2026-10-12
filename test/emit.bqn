# test/emit.bqn: differential tests of the compiled primitives against CBQN.
#
#   bqn test/emit.bqn [cases per test] [seed]
#
# Compiles src/prims.bqn, plus a definition per test from test/gen.bqn, to C;
# builds src/vm.c with it as the test harness; runs every case through the
# binary and through CBQN's built-ins; and reports as test/prims.bqn does.
# Also regenerates src/gen/prims.c, the checked-in output for prims alone.

Arg ← {𝕨 𝕊 i: i < ≠•args ? •ParseFloat i⊑•args ; 𝕨 𝕊 i: 𝕨}
cases ← 200 Arg 0
g ← (1 Arg 1) •Import "gen.bqn"
c ← •Import "../src/c.bqn"
root ← •path∾"/.."
nl ← @+10

Sh ← {
  code‿out‿err ← 𝕨 •SH 𝕩
  (∾ ⟨"command failed: ", ∾' '⊸∾¨𝕩, ⟨nl⟩, err⟩) ! code=0
  out
}

prims ← •FChars root∾"/src/prims.bqn"
(root∾"/src/gen/prims.c") •FChars c.Compile prims
{•file.CreateDir⍟(¬•file.Exists) root∾𝕩}¨ "/build"‿"/build/gen"
(root∾"/build/gen/prims_test.c") •FChars c.Compile prims ∾ g.Defs @
bin ← root∾"/build/prims-test"
@ ⊣ {⇐} Sh ⟨"cc", "-std=c11", "-O1", "-w", "-DPRIM_TEST", "-DGEN_FILE=""../build/gen/prims_test.c""", root∾"/src/vm.c", "-o", bin, "-lm"⟩

args ← g.Cases cases
lines ← ∾ (↕≠args) {i←𝕨 ⋄ {"t"∾(•Fmt i)∾" "∾(•Fmt ≠𝕩)∾∾(' '∾g.Ser)¨𝕩}¨ 𝕩}¨ args
out ← {stdin ⇐ ∾ lines ∾¨ nl} Sh ⟨bin⟩
outs ← (nl⊸≠⊸/)¨ (+`»out=nl) ⊔ out
"harness gave a different number of results" ! (≠outs) = ≠lines
ours ← (/≠¨args) ⊔ g.Result¨ outs
res ← {𝕊 src‿as‿os: theirs ← •BQN src ⋄ os {⟨𝕨, g.Try theirs‿𝕩⟩}¨ as}¨ <˘⍉> (1⊑¨g.tests)‿args‿ours
bad ← args g.Report res
•Exit 0 < bad
