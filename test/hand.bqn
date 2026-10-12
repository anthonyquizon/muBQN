# test/hand.bqn: differential tests of the hand-written VM (src/vm.aq.c)
# against CBQN.
#
#   bqn test/hand.bqn [cases per test] [seed] [test name...]
#
# Test names are as listed in test/gen.bqn, such as "𝕨+𝕩" or "+´𝕩"; with
# none, it runs those two. Builds src/vm.aq.c into test/hand_main.c's harness
# with AddressSanitizer, runs every case through it and through CBQN, and
# reports as test/emit.bqn does, plus any case that leaked objects.

Arg ← {𝕨 𝕊 i: i < ≠•args ? •ParseFloat i⊑•args ; 𝕨 𝕊 i: 𝕨}
cases ← 200 Arg 0
g ← (1 Arg 1) •Import "gen.bqn"
names ← {0=≠𝕩 ? ⟨"𝕨+𝕩", "+´𝕩"⟩ ; 𝕩} 2↓•args
root ← •path∾"/.."
nl ← @+10

Sh ← {
  code‿out‿err ← 𝕨 •SH 𝕩
  (∾ ⟨"command failed: ", ∾' '⊸∾¨𝕩, ⟨nl⟩, err⟩) ! code=0
  out
}

known ← ⊑¨g.tests
{(∾ ⟨"no test named ", 𝕩, "; see the list in test/gen.bqn"⟩) ! ∨´ known ≡¨ <𝕩}¨ names
ts ← (known ∊ names) / g.tests

•file.CreateDir⍟(¬•file.Exists) root∾"/build"
bin ← root∾"/build/hand-test"
@ ⊣ {⇐} Sh ⟨"cc", "-std=c11", "-g", "-O1", "-DHAND_TEST", "-fsanitize=address,undefined", root∾"/test/hand_main.c", "-o", bin, "-lm"⟩

args ← {𝕊 name‿src‿gen: Gen¨ cases⥊@}¨ ts
lines ← ∾ (1⊑¨ts) {src←𝕨 ⋄ {src∾" "∾(•Fmt ≠𝕩)∾∾(' '∾g.Ser)¨𝕩}¨ 𝕩}¨ args
code‿out‿err ← {stdin ⇐ ∾ lines ∾¨ nl} •SH ⟨bin⟩
outs ← (nl⊸≠⊸/)¨ (+`»out=nl) ⊔ out
{𝕤   # a crash (such as an AddressSanitizer report) ends the run: show the case
  •Out err
  •Out "crashed on case: "∾(≠outs)⊑lines
  •Exit 1
}⍟(code≠0) @
"harness gave a different number of results" ! (≠outs) = ≠lines

Leak ← {   # "leak <n> <rest>" → ⟨n, rest⟩
  "leak " ≡ 5↑𝕩 ? r ← 5↓𝕩 ⋄ k ← ⊑r⊐' ' ⋄ ⟨•ParseFloat k↑r, (k+1)↓r⟩ ;
  ⟨0, 𝕩⟩
}
leaks‿rest ← <˘⍉> Leak¨ outs
Per ← (/≠¨args)⊸⊔
ours ← Per g.Result¨ rest
res ← {𝕊 src‿as‿os: theirs ← •BQN src ⋄ os {⟨𝕨, g.Try theirs‿𝕩⟩}¨ as}¨ <˘⍉> (1⊑¨ts)‿args‿ours
bad ← ts g.ReportFor args‿res

leaky ← 0
{𝕊 name‿as‿ls:
  m ← 0 < ls
  leaky +↩ +´m
  {𝕤 ⋄ •Out name∾": "∾(•Fmt +´m)∾" cases leaked, e.g. "∾•Fmt ⊑m/as}⍟(∨´m) @
}¨ <˘⍉> (⊑¨ts)‿args‿(Per leaks)
•Exit 0 < bad + leaky
