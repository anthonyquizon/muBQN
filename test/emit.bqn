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
•file.CreateDir⍟(¬•file.Exists) root∾"/build/gen"
(root∾"/build/gen/prims_test.c") •FChars c.Compile prims ∾ g.Defs @
bin ← root∾"/build/prims-test"
@ ⊣ {⇐} Sh ⟨"cc", "-std=c11", "-O1", "-w", "-DPRIM_TEST", "-DGEN_FILE=""../build/gen/prims_test.c""", root∾"/src/vm.c", "-o", bin, "-lm"⟩

# ---- serialization, matching the harness in src/vm.c
FmtN ← {𝕩≠𝕩 ? "nan" ; 𝕩=∞ ? "inf" ; 𝕩=-∞ ? "-inf" ; {𝕩='¯' ? '-' ; 𝕩}¨ •Repr 𝕩}
Ser ← {
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
Result ← {   # a line of output → ⟨1, value⟩ or ⟨0, message⟩
  "ok " ≡ 3↑𝕩 ? ⟨1, De 3↓𝕩⟩ ;
  "err " ≡ 4↑𝕩 ? ⟨0, 4↓𝕩⟩ ;
  ⟨0, "harness: "∾𝕩⟩
}

args ← g.Cases cases
lines ← ∾ (↕≠args) {i←𝕨 ⋄ {"t"∾(•Fmt i)∾" "∾(•Fmt ≠𝕩)∾∾(' '∾Ser)¨𝕩}¨ 𝕩}¨ args
out ← {stdin ⇐ ∾ lines ∾¨ nl} Sh ⟨bin⟩
outs ← (nl⊸≠⊸/)¨ (+`»out=nl) ⊔ out
"harness gave a different number of results" ! (≠outs) = ≠lines
ours ← (/≠¨args) ⊔ Result¨ outs
res ← {𝕊 src‿as‿os: theirs ← •BQN src ⋄ os {⟨𝕨, g.Try theirs‿𝕩⟩}¨ as}¨ <˘⍉> (1⊑¨g.tests)‿args‿ours
bad ← args g.Report res
•Exit 0 < bad
