# dialect.bqn: front end for the primitive dialect (see docs/design.md).
#
# Rewrites each primitive glyph to the name of its dialect definition and
# checks the dependency rule: a top-level definition may only use glyphs whose
# definitions come earlier in the file. The rewritten source keeps the original
# line structure, so error line numbers still match.
#
#   Check src       → rewritten source; errors name the line and glyph
#   Load file       → namespace of src/file, run on CBQN with b.bqn as •args
#   name LoadSrc s  → the same for source text s

# ---- glyphs. Each one has a fixed name; the case and underscores give the
# role, as BQN requires.
names ← ⟨
  "+Plus", "-Minus", "×Times", "÷Divide", "⋆Power", "√Root", "⌊Floor", "⌈Ceil"
  "|Abs", "¬Not", "∧And", "∨Or", "<Less", ">Greater", "≠NotEq", "=Equal"
  "≤LessEq", "≥GreaterEq", "≡Match", "≢Shape", "⥊Reshape", "∾Join", "≍Couple"
  "⋈Pair", "↑Take", "↓Drop", "↕Range", "«ShiftB", "»ShiftA", "⌽Reverse"
  "⍉Transpose", "/Replicate", "⍋GradeUp", "⍒GradeDown", "⊏Select", "⊑Pick"
  "⊐IndexOf", "⊒ProgIndex", "∊Member", "⍷Find", "⊔Group"
  "˘_cells", "¨_each", "⌜_table", "⁼_undo", "´_fold", "˝_insert", "`_scan"
  "⌾_under_", "⎉_rank_", "⚇_depth_"
⟩
glyphs ← ⊑¨names
gnames ← 1↓¨names
# Not rewritten, so they keep their BQN meaning: ∘ ○ ⊸ ⟜ ˜ ˙ ⊘ ◶ ⊢ ⊣ ! ⍟.
# The compiler handles these itself.
excluded ← "⎊"

nl ← @+10

# ---- lexing: 1 where a character is code, 0 inside strings, character
# literals and comments.
CodeMask ← {
  src ← 𝕩 ⋄ n ← ≠src ⋄ m ← n⥊1 ⋄ i ← 0
  Skip ← {m ↩ 0¨⌾(((n-i)⌊𝕩)↑i↓⊢) m ⋄ i +↩ 𝕩}
  Q ← {𝕩<n ? '"'=𝕩⊑src ; 0}
  StrLen ← {𝕤  # string literal at i, quotes included; "" is an escaped quote
    j ← i+1
    {𝕤 ⋄ j +↩ 1 + Q j}•_while_{𝕤 ⋄ (j<n) ∧ (¬Q j) ∨ Q j+1} @
    "unterminated string" ! j<n
    1+j-i
  }
  Step ← {  # 𝕩 is the character at i
    𝕊 '"': Skip StrLen @ ;
    𝕊 ''': Skip 3 ;
    𝕊 '#': Skip ⊑(i↓src)⊐nl ;
    𝕊 c: i +↩ 1
  }
  {𝕤 ⋄ Step i⊑src}•_while_{𝕤 ⋄ i<n} @
  m
}

# ---- definitions: a line that starts in column 0 with a name followed by
# ← or ⇐ begins a new definition. Returns the name, or "" for other lines.
identChars ← "_"∾('a'+↕26)∾('A'+↕26)∾'0'+↕10
LineDef ← {
  w ← ⊑(𝕩 ∊ "←⇐")⊐1
  lhs ← (' '⊸≠/⊢) w↑𝕩
  ok ← (w<≠𝕩) ∧ (0<≠lhs) ∧ (∧´lhs ∊ identChars) ∧ ' '≠⊑𝕩∾' '
  ok ? lhs ; ""
}

Check ⇐ {
  src ← 𝕩
  m ← CodeMask src
  lno ← +`nl=src                      # line of each char; a newline starts its line
  lines ← lno ⊔ src
  lmask ← lno ⊔ m
  defs ← LineDef¨ (nl⊸≠/⊢)¨ lines
  isDef ← 0<≠¨defs
  owner ← ¯1 + +`isDef                # definition each line belongs to; ¯1 = header
  defined ← isDef/defs
  Rewrite ← {𝕊 ln:
    line ← ln⊑lines ⋄ mask ← ln⊑lmask ⋄ own ← ln⊑owner
    At ← {"line "∾(•Fmt ln+1)∾": "∾𝕩}
    (At "⎊ is not allowed in the dialect") ! ¬∨´mask ∧ line ∊ excluded
    sys ← /mask ∧ '•'=line
    (At "• is only allowed as •args") ! ∧´{"args"≡4↑(𝕩+1)↓line}¨ sys
    used ← mask ∧ line ∊ glyphs
    u ← used/line
    nm ← gnames ⊏˜ glyphs ⊐ u
    before ← (0⌈own)↑defined
    bad ← ¬nm ∊ before
    {𝕤
      g ← ⊑bad/u ⋄ n ← ⊑bad/nm
      self ← (0≤own) ∧ n≡own⊑defined∾<""
      (At ⟨g⟩∾" ("∾n∾") is used "∾self⊑⟨"before its definition", "in its own definition; use 𝕊"⟩) ! 0
    }⍟(∨´bad) @
    ∾ used {𝕨 ? " "∾(gnames⊑˜⊑glyphs⊐⋈𝕩)∾" " ; ⋈𝕩}¨ line
  }
  ∾ Rewrite¨ ↕≠lines
}

# name LoadSrc src: like Load, for source text; name names the output file
LoadSrc ⇐ {
  b ← •Import "b.bqn"
  dir ← •path∾"/../build"
  •file.CreateDir⍟(¬•file.Exists) dir
  out ← dir∾"/"∾𝕨∾".gen.bqn"
  out •FChars Check 𝕩
  b •Import out
}
Load ⇐ {𝕩 LoadSrc •FChars •path∾"/"∾𝕩}
