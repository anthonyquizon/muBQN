# c.bqn: compiler from the primitive dialect to C (see docs/design.md).
#
#   Lex src         → tokens ⟨kind, text, line⟩
#   Parse tokens    → program: a list of statements
#   Gen program     → C source for src/gen/, included by vm.c
#   Compile src     → Gen Parse Lex (dialect.Check src)
#
# Milestone 1: no reference counting. Values are never freed.

d ← •Import "dialect.bqn"

nl ← @+10
Has ← {⊑(⥊𝕨) ∊ 𝕩}                   # char Has string
In ← {⊑(<𝕨) ∊ 𝕩}                     # string In list of strings
letters ← ('a'+↕26)∾'A'+↕26
digits ← '0'+↕10
Norm ← {(𝕩≠'_') / 𝕩 + 32×(𝕩≥'A')∧𝕩≤'Z'}   # BQN ignores case and underscores
Role ← {
  𝕊 s: ('_'=⊑s) ∧ ('_'=¯1⊑s) ∧ 1<≠s ? "m2" ;
  𝕊 s: '_'=⊑s ? "m1" ;
  𝕊 s: (⊑s) Has 'A'+↕26 ? "f" ;
  𝕊 s: "s"
}

# ---- lexing
specChars ← "𝕨𝕩𝕗𝕘𝕤𝕎𝕏𝔽𝔾𝕊𝕣"
puncts ← "(){}⟨⟩[]‿;:?←⇐↩.·"
primChars ← "∘○⊸⟜˜˙⊘◶⊢⊣!⍟"

Lex ⇐ {
  src ← 𝕩 ⋄ n ← ≠src ⋄ i ← 0 ⋄ line ← 1 ⋄ out ← ⟨⟩
  At ← {𝕩<n ? 𝕩⊑src ; @}
  Push ← {out ∾↩ <𝕩∾<line ⋄ @}
  Span ← {𝕊 set: j ← i ⋄ {𝕤 ⋄ j +↩ 1}•_while_{𝕤 ⋄ (At j) Has set} @ ⋄ j}
  Str ← {𝕤
    s ← "" ⋄ j ← i+1
    {𝕤 ⋄ ('"'=At j) ◶ ⟨{𝕤 ⋄ s ∾↩ At j ⋄ j +↩ 1}, {𝕤 ⋄ s ∾↩ '"' ⋄ j +↩ 2}⟩ @}•_while_{𝕤 ⋄ (j<n) ∧ ('"'≠At j) ∨ '"'=At j+1} @
    "unterminated string" ! j<n
    Push "str"‿s ⋄ i ↩ j+1
  }
  DigitsFrom ← {j ← 𝕩 ⋄ {𝕤 ⋄ j +↩ 1}•_while_{𝕤 ⋄ (At j) Has digits} @ ⋄ j}
  NumEnd ← {   # end of the number whose digits start at 𝕩
    (At 𝕩) Has "∞π" ? 𝕩+1 ;
    k ← DigitsFrom 𝕩
    k ↩ {('.'=At k) ∧ (At k+1) Has digits ? DigitsFrom k+1 ; k}
    {(At k) Has "eE" ? DigitsFrom k + 1 + '¯'=At k+1 ; k}
  }
  Step ← {
    𝕊 c: c Has " "∾@+9 ? i +↩ 1 ;
    𝕊 c: c = nl ? Push "sep"‿nl ⋄ line +↩ 1 ⋄ i +↩ 1 ;
    𝕊 c: c Has "⋄," ? Push "sep"‿c ⋄ i +↩ 1 ;
    𝕊 c: c = '#' ? i ↩ i + ⊑(i↓src) ⊐ nl ;
    𝕊 c: c = '"' ? Str @ ;
    𝕊 c: c = ''' ? Push "chr"‿(At i+1) ⋄ i +↩ 3 ;
    𝕊 c: c = '@' ? Push "chr"‿@ ⋄ i +↩ 1 ;
    𝕊 c: (c Has digits∾"∞π") ∨ (c='¯') ∧ (At i+1) Has digits∾"∞π" ?
      j ← NumEnd i + c='¯'
      Push "num"‿(i↓j↑src) ⋄ i ↩ j ;
    𝕊 c: (c='_') ∧ '𝕣'=At i+1 ?
      t ← "_𝕣" ∾ ('_'=At i+2) / "_"
      Push "spec"‿t ⋄ i +↩ ≠t ;
    𝕊 c: c Has letters∾"_" ?
      j ← i ⋄ {𝕤 ⋄ j +↩ 1}•_while_{𝕤 ⋄ (At j) Has letters∾digits∾"_"} @
      Push "name"‿(i↓j↑src) ⋄ i ↩ j ;
    𝕊 c: c Has specChars ? Push "spec"‿⟨c⟩ ⋄ i +↩ 1 ;
    𝕊 c: c = '•' ?
      j ← i+1 ⋄ {𝕤 ⋄ j +↩ 1}•_while_{𝕤 ⋄ (At j) Has letters∾digits∾"_"} @
      Push "sys"‿(i↓j↑src) ⋄ i ↩ j ;
    𝕊 c: c Has puncts ? Push "p"‿c ⋄ i +↩ 1 ;
    𝕊 c: c Has primChars ? Push "prim"‿c ⋄ i +↩ 1 ;
    𝕊 c: ("line "∾(•Fmt line)∾": unexpected character "∾⟨c⟩) ! 0
  }
  {𝕤 ⋄ Step i⊑src}•_while_{𝕤 ⋄ i<n} @
  out
}

# ---- parsing. A term is ⟨role, node⟩; roles are "s" "f" "m1" "m2".
#
# Nodes:  num text | chr c | str s | var name raw | spec s | prim c | sys s
#         field node name raw | list nodes | nothing
#         call1 f x | call2 f w x | mod1 m f | mod2 m f g | atop g h | fork f g h
#         assign arrow lhs rhs | block type bodies
# A body is ⟨header, statements⟩; a statement is ⟨"expr"|"pred", node⟩.
# A header is ⟨kind, w, x, f, g⟩ with ⟨⟩ for absent parts.

PrimRoles ← {
  𝕊 c: c Has "⊢⊣!" ? "f" ;
  𝕊 c: c Has "˜˙" ? "m1" ;
  𝕊 c: "m2"
}
SpecRole ← {
  𝕊 s: s ≡ "_𝕣" ? "m1" ;
  𝕊 s: s ≡ "_𝕣_" ? "m2" ;
  𝕊 s: (⊑s) Has "𝕎𝕏𝔽𝔾𝕊" ? "f" ;
  𝕊 s: "s"
}

Parse ⇐ {
  toks ← 𝕩 ⋄ i ← 0 ⋄ n ← ≠toks
  T ← {𝕤 ⋄ i<n ? i⊑toks ; ⟨"eof", ' ', (0<n) ◶ ⟨1, {𝕤⋄2⊑¯1⊑toks}⟩ @⟩}
  K ← {𝕤 ⋄ ⊑T@}
  X ← {𝕤 ⋄ 1⊑T@}
  Adv ← {𝕤 ⋄ i +↩ 1 ⋄ @}
  IsP ← {("p"≡K@) ∧ 𝕩≡X@}
  Err ← {("line "∾(•Fmt 2⊑T@)∾": "∾𝕩) ! 0}
  Expect ← {IsP 𝕩 ? Adv@ ; Err "expected "∾⟨𝕩⟩}
  ender ← ")}⟩;:?←⇐↩"
  AtEnd ← {𝕤 ⋄ k ← K@ ⋄ (k≡"sep") ∨ (k≡"eof") ∨ ("p"≡k) ∧ (X@) Has ender}
  SkipSeps ← {𝕤 ⋄ {𝕤 ⋄ Adv@}•_while_{𝕤 ⋄ "sep"≡K@} @}

  # special names used directly in each open block, innermost last
  used ← ⟨⟩
  Note ← {used ↩ (¯1↓used) ∾ <(¯1⊑used) ∾ <𝕩}⍟{𝕤 ⋄ 0<≠used}

  Atom ← {
    𝕊: "num" ≡ K@ ? t ← X@ ⋄ Adv@ ⋄ ⟨"s", ⟨"num", t⟩⟩ ;
    𝕊: "chr" ≡ K@ ? t ← X@ ⋄ Adv@ ⋄ ⟨"s", ⟨"chr", t⟩⟩ ;
    𝕊: "str" ≡ K@ ? t ← X@ ⋄ Adv@ ⋄ ⟨"s", ⟨"str", t⟩⟩ ;
    𝕊: "sys" ≡ K@ ? t ← X@ ⋄ Adv@ ⋄ ⟨"s", ⟨"sys", t⟩⟩ ;
    𝕊: "prim" ≡ K@ ? t ← X@ ⋄ Adv@ ⋄ ⟨PrimRoles t, ⟨"prim", t⟩⟩ ;
    𝕊: "spec" ≡ K@ ? t ← X@ ⋄ Adv@ ⋄ Note t ⋄ ⟨SpecRole t, ⟨"spec", t⟩⟩ ;
    𝕊: "name" ≡ K@ ?
      t ← X@ ⋄ Adv@
      r ← Role t ⋄ node ← ⟨"var", Norm t, t⟩
      {𝕤
        Adv@ ⋄ "field name expected after ." ! "name" ≡ K@
        f ← X@ ⋄ Adv@ ⋄ r ↩ Role f ⋄ node ↩ ⟨"field", node, Norm f, f⟩
      }•_while_{𝕤 ⋄ IsP '.'} @
      ⟨r, node⟩ ;
    𝕊: IsP '(' ? Adv@ ⋄ e ← Expr@ ⋄ Expect ')' ⋄ {"none"≡⊑e ? Err "empty parentheses" ; e} ;
    𝕊: IsP '{' ? Block@ ;
    𝕊: IsP '⟨' ?
      Adv@ ⋄ items ← ⟨⟩
      {𝕤 ⋄ items ∾↩ <1⊑Expr@}•_while_{𝕤 ⋄ SkipSeps@ ⋄ ¬IsP '⟩'} @
      Adv@ ⋄ ⟨"s", ⟨"list", items⟩⟩ ;
    𝕊: IsP '·' ? Adv@ ⋄ ⟨"s", ⟨"nothing"⟩⟩ ;
    𝕊: Err "unexpected "∾•Fmt X@
  }
  Strand ← {
    items ← ⟨1⊑𝕩⟩
    {𝕤 ⋄ Adv@ ⋄ items ∾↩ <1⊑Atom@}•_while_{𝕤 ⋄ IsP '‿'} @
    ⟨"s", ⟨"list", items⟩⟩
  }
  Term ← {𝕤 ⋄ t ← Atom@ ⋄ (IsP '‿') ◶ ⟨⊢, Strand⟩ t}

  # modifiers bind first, left to right; then application and trains, right
  # to left
  Mods ← {   # apply modifiers, left to right
    ts ← 𝕩 ⋄ out ← ⟨⟩ ⋄ j ← 0
    {𝕤
      r ← ⊑j⊑ts
      {
        r ≡ "m1" ?
          "a 1-modifier needs an operand on its left" ! 0<≠out
          op ← ¯1⊑out ⋄ out ↩ (¯1↓out) ∾ <⟨"f", ⟨"mod1", 1⊑j⊑ts, 1⊑op⟩⟩ ⋄ j +↩ 1 ;
        r ≡ "m2" ?
          "a 2-modifier needs operands on both sides" ! (0<≠out) ∧ (j+1)<≠ts
          op ← ¯1⊑out ⋄ g ← (j+1)⊑ts
          out ↩ (¯1↓out) ∾ <⟨"f", ⟨"mod2", 1⊑j⊑ts, 1⊑op, 1⊑g⟩⟩ ⋄ j +↩ 2 ;
        out ∾↩ <j⊑ts ⋄ j +↩ 1
      }
    }•_while_{𝕤 ⋄ j < ≠ts} @
    out
  }
  Apply ← {   # then application and trains, right to left
    𝕊 out: 1 = ≠out ? ⊑out ;
    𝕊 out: "s" ≡ ⊑¯1⊑out ?
      v ← 1⊑¯1⊑out ⋄ k ← (≠out)-2
      {𝕤
        {"f" ≡ ⊑k⊑out ? @ ; Err "double subjects (missing ‿?)"}
        f ← 1⊑k⊑out
        {(k≥1) ∧ "s" ≡ ⊑(k-1)⊑out ?
          w ← 1⊑(k-1)⊑out
          v ↩ ("nothing"≡⊑w) ⊑ ⟨⟨"call2", f, w, v⟩, ⟨"call1", f, v⟩⟩ ⋄ k -↩ 2 ;
          v ↩ ⟨"call1", f, v⟩ ⋄ k -↩ 1
        }
      }•_while_{𝕤 ⋄ k ≥ 0} @
      ⟨"s", v⟩ ;
    𝕊 out:
      "a train must end in a function" ! "f" ≡ ⊑¯1⊑out
      v ← 1⊑¯1⊑out ⋄ k ← (≠out)-2
      {𝕤
        "a train needs functions in odd positions from the right" ! "f" ≡ ⊑k⊑out
        g ← 1⊑k⊑out
        {k≥1 ? f ← 1⊑(k-1)⊑out ⋄ v ↩ ⟨"fork", f, g, v⟩ ⋄ k -↩ 2 ;
          v ↩ ⟨"atop", g, v⟩ ⋄ k -↩ 1}
      }•_while_{𝕤 ⋄ k ≥ 0} @
      ⟨"f", v⟩
  }
  Reduce ← {0 = ≠𝕩 ? ⟨"none", ⟨"nothing"⟩⟩ ; 1 = ≠𝕩 ? ⊑𝕩 ; Apply Mods 𝕩}

  Expr ← {𝕤
    terms ← ⟨⟩
    {𝕤 ⋄ terms ∾↩ <Term@}•_while_{𝕤 ⋄ ¬AtEnd@} @
    {𝕤
      a ← X@ ⋄ Adv@
      {(a='↩') ∧ (2≤≠terms) ∧ "f" ≡ ⊑¯1⊑terms ?    # x F↩ y
        lhs ← 1⊑¯2⊑terms ⋄ f ← 1⊑¯1⊑terms
        rhs ← AtEnd◶⟨{𝕤 ⋄ ⟨"call2", f, lhs, 1⊑Expr@⟩}, {𝕤 ⋄ ⟨"call1", f, lhs⟩}⟩ @
        terms ↩ (¯2↓terms) ∾ <⟨"s", ⟨"assign", '↩', lhs, rhs⟩⟩ ;
        "assignment needs a target" ! 0<≠terms
        lhs ← ¯1⊑terms ⋄ rhs ← Expr@
        "assignment needs a value" ! "none" ≢ ⊑rhs
        terms ↩ (¯1↓terms) ∾ <⟨⊑rhs, ⟨"assign", a, 1⊑lhs, 1⊑rhs⟩⟩
      }
    }⍟{𝕤 ⋄ ("p"≡K@) ∧ (X@) Has "←⇐↩"} @
    Reduce terms
  }

  HasHeader ← {𝕤   # is there a ':' at depth 0 before the end of this body?
    j ← i ⋄ depth ← 0 ⋄ res ← ¯1
    {𝕤
      t ← j⊑toks ⋄ k ← ⊑t ⋄ c ← 1⊑t
      {
        𝕊: (k≡"p") ∧ c Has "({⟨" ? depth +↩ 1 ;
        𝕊: (k≡"p") ∧ c Has ")}⟩" ? depth -↩ 1 ⋄ res ↩ 0⌈res ;
        𝕊: (depth=0) ∧ (k≡"p") ∧ c≡':' ? res ↩ 1 ;
        𝕊: (depth=0) ∧ (k≡"sep") ∨ (k≡"p") ∧ c Has ";?←⇐↩" ? res ↩ 0 ;
        𝕊: @
      } @
      j +↩ 1
    }•_while_{𝕤 ⋄ (j<n) ∧ (res<0) ∧ depth≥0} @
    res = 1
  }
  Header ← {𝕤
    terms ← ⟨⟩
    {𝕤 ⋄ terms ∾↩ <Term@}•_while_{𝕤 ⋄ ¬IsP ':'} @
    Adv@
    nodes ← 1⊑¨terms ⋄ roles ← ⊑¨terms
    IsSelf ← {"spec"≡⊑𝕩 ? (1⊑𝕩) In "𝕊"‿"_𝕣"‿"_𝕣_" ; 0}
    p ← ⊑ (IsSelf¨nodes) ⊐ 1
    "header needs 𝕊, _𝕣 or _𝕣_" ! p < ≠nodes
    s ← 1⊑p⊑nodes
    Opt ← {(𝕩≥0) ∧ 𝕩<≠nodes ? 𝕩⊑nodes ; ⟨⟩}
    {
      𝕊: s≡"𝕊" ? ⟨"fn", Opt p-1, Opt p+1, ⟨⟩, ⟨⟩⟩ ;
      𝕊: s≡"_𝕣" ? ⟨"m1", Opt p-2, Opt p+1, Opt p-1, ⟨⟩⟩ ;
      𝕊: ⟨"m2", Opt p-2, Opt p+2, Opt p-1, Opt p+1⟩
    } @
  }
  Body ← {𝕤
    SkipSeps@
    hdr ← HasHeader◶⟨⟨⟩, Header⟩ @
    stmts ← ⟨⟩
    {𝕤
      e ← Expr@
      "empty statement" ! "none" ≢ ⊑e
      stmts ∾↩ <⟨(IsP '?') ⊑ "expr"‿"pred", 1⊑e⟩
      Adv⍟{𝕤 ⋄ IsP '?'} @
      SkipSeps@
    }•_while_{𝕤 ⋄ SkipSeps@ ⋄ ¬(IsP ';') ∨ IsP '}'} @
    ⟨hdr, stmts⟩
  }
  Block ← {𝕤
    Adv@ ⋄ used ∾↩ <⟨⟩
    bodies ← ⟨Body@⟩
    {𝕤 ⋄ Adv@ ⋄ bodies ∾↩ <Body@}•_while_{𝕤 ⋄ IsP ';'} @
    Expect '}'
    sp ← ¯1⊑used ⋄ used ↩ ¯1↓used
    hk ← ⊑¨ (0<≠¨⊑¨bodies) / ⊑¨bodies       # header kinds
    U ← {∨´ 𝕩 ∊ sp}
    type ← {
      ("m2" In hk) ∨ U "𝔾"‿"𝕘"‿"_𝕣_" ? "m2" ;
      ("m1" In hk) ∨ U "𝔽"‿"𝕗"‿"_𝕣" ? "m1" ;
      ("fn" In hk) ∨ U "𝕨"‿"𝕩"‿"𝕤"‿"𝕊"‿"𝕎"‿"𝕏" ? "fn" ;
      "imm"
    }
    deferred ← (0<≠hk) ∨ U "𝕨"‿"𝕩"‿"𝕤"‿"𝕊"
    role ← (⊑"fn"‿"m1"‿"m2"‿"imm" ⊐ <type) ⊑ "f"‿"m1"‿"m2"‿"s"
    ⟨role, ⟨"block", type, deferred, bodies⟩⟩
  }

  stmts ← ⟨⟩
  {𝕤 ⋄ e ← Expr@ ⋄ stmts ∾↩ <1⊑e ⋄ SkipSeps@}•_while_{𝕤 ⋄ SkipSeps@ ⋄ "eof" ≢ K@} @
  stmts
}

# ---- unparsing: a node back to BQN source, fully parenthesized. Running
# the tests on Unparse Parse of a file checks the parser's structure.
JoinWith ← {0=≠𝕩 ? "" ; (⊑𝕩) ∾ ∾ 𝕨⊸∾¨ 1↓𝕩}
Unparse ⇐ {
  P ← {"("∾𝕩∾")"}
  Pat ← {"list"≡⊑𝕩 ? "⟨"∾(", " JoinWith Unparse¨1⊑𝕩)∾"⟩" ; Unparse 𝕩}
  Hdr ← {
    𝕊 ⟨⟩: "" ;
    𝕊 k‿w‿x‿f‿g:
      O ← {0=≠𝕩 ? "" ; " "∾Pat 𝕩}
      self ← (⊑"fn"‿"m1"‿"m2" ⊐ <k) ◶ ⟨"𝕊", {𝕤⋄(Unparse f)∾" _𝕣"}, {𝕤⋄(Unparse f)∾" _𝕣_ "∾Unparse g}⟩ @
      (O w)∾" "∾self∾(O x)∾": "
  }
  Stmts ← {∾ {𝕊 k‿e: (Unparse e)∾("pred"≡k) ⊑ " ⋄ "‿" ? "}¨ 𝕩}
  Body ← {𝕊 h‿st: (Hdr h)∾Stmts st}
  {
    𝕊 "num"‿t: t ;
    𝕊 "chr"‿c: (c=@) ⊑ ⟨"'"∾c∾"'", "@"⟩ ;
    𝕊 "str"‿s: '"' ∾ ('"' (⊢∾=⊸/) s)∾'"' ;
    𝕊 "var"‿n‿r: r ;
    𝕊 "spec"‿s: s ;
    𝕊 "prim"‿c: ⟨c⟩ ;
    𝕊 "sys"‿s: s ;
    𝕊 "field"‿ns‿n‿r: (Unparse ns)∾"."∾r ;
    𝕊 ⟨"nothing"⟩: "·" ;
    𝕊 "list"‿items: "⟨"∾(", " JoinWith Unparse¨items)∾"⟩" ;
    𝕊 "call1"‿f‿x: P (P Unparse f)∾" "∾P Unparse x ;
    𝕊 "call2"‿f‿w‿x: P (P Unparse w)∾" "∾(P Unparse f)∾" "∾P Unparse x ;
    𝕊 "mod1"‿m‿f: P (P Unparse f)∾" "∾Unparse m ;
    𝕊 "mod2"‿m‿f‿g: P (P Unparse f)∾" "∾(Unparse m)∾" "∾P Unparse g ;
    𝕊 "atop"‿g‿h: P (P Unparse g)∾" "∾P Unparse h ;
    𝕊 "fork"‿f‿g‿h: P (P Unparse f)∾" "∾(P Unparse g)∾" "∾P Unparse h ;
    𝕊 "assign"‿a‿l‿r: (Pat l)∾" "∾a∾" "∾Unparse r ;
    𝕊 "block"‿t‿df‿bodies: "{"∾((nl∾";"∾nl) JoinWith Body¨bodies)∾"}"
  } 𝕩
}

# ---- C generation
#
# Every block body becomes part of a C function; every intermediate value
# gets a temporary. Calls are direct when the callee is known statically: a
# top-level function or modifier, a basis operation, 𝕊, or a combinator
# applied on the spot. Anything used as a value becomes a runtime object.
#
#   F_x(B *e, B w, B x)   top-level function; w is NONE when called monadically
#   M_x(B *e, B w, B x)   deferred modifier; e holds the operands
#   MI_x(B f0[, B g0])    immediate modifier: returns the derived value
#   L_n(B *e, B w, B x)   local block; e holds captured values
#   b_x(B w, B x)         basis operation b.x, in vm.c
#   bm_x(B f, B w, B x)   basis modifier b._x, in vm.c
#
# Note on style: each ; body of a BQN block has its own scope, so every body
# below has a full header, and decisions inside a body use an inner block.

CNum ← {∾ {𝕩='¯' ? "-" ; 𝕩='∞' ? "INFINITY" ; 𝕩='π' ? "M_PI" ; ⟨𝕩⟩}¨ 𝕩}
Lines ← {∾ 𝕩 ∾¨ <nl}
primNames ← "∘○⊸⟜˜˙⊘◶⍟⊢⊣!"
primCnames ← "D_atop2"‿"D_over"‿"D_before"‿"D_after"‿"D_swap"‿"D_const"‿"D_valences"‿"D_choose"‿"D_repeat"‿"P_right"‿"P_left"‿"P_assert"
PrimC ← {(⊑primNames ⊐ 𝕩) ⊑ primCnames}
Ops ← {"(B[]){"∾(", " JoinWith 𝕩)∾"}"}
Args ← {", " JoinWith 𝕩}

Gen ⇐ {
  prog ← 𝕩
  globals ← ⟨⟩      # ⟨name, kind, cname⟩; kind: fn m1d m2d m1i m2i b
  strs ← ⟨⟩ ⋄ bvals ← ⟨⟩ ⋄ bmods ← ⟨⟩ ⋄ nlocal ← 0
  protos ← ⟨⟩ ⋄ defs ← ⟨⟩ ⋄ inits ← ⟨⟩ ⋄ exports ← ⟨⟩

  IsGlobal ← {(⊑ (⊑¨globals) ⊐ <𝕩) < ≠globals}
  GlobalInfo ← {(⊑ (⊑¨globals) ⊐ <𝕩) ⊑ globals}
  Str ← {i ← ⊑ strs ⊐ <𝕩 ⋄ strs ∾↩ (i=≠strs) / ⟨𝕩⟩ ⋄ "S"∾•Fmt i}
  BVal ← {bvals ∾↩ (¬𝕩 In bvals) / ⟨𝕩⟩ ⋄ "BV_"∾𝕩}
  BMod ← {bmods ∾↩ (¬𝕩 In bmods) / ⟨𝕩⟩ ⋄ "BM_"∾𝕩}

  # A function context: one C function being written.
  #   fkind: fn m1 m2 local imm1 imm2; cname: its C name
  NewFC ← {𝕊 par‿k‿self:
    ls ← ⟨⟩ ⋄ ntmp ← 0 ⋄ nvar ← 0 ⋄ frames ← ⟨⟨⟩⟩ ⋄ cs ← ⟨⟩
    kind ⇐ "fc" ⋄ parent ⇐ par ⋄ fkind ⇐ k ⋄ cname ⇐ self
    Emit ⇐ {ls ∾↩ <𝕩 ⋄ @}
    Lines ⇐ {𝕤 ⋄ ls}
    Tmp ⇐ {ntmp +↩ 1 ⋄ t ← "t"∾•Fmt ntmp ⋄ Emit "  B "∾t∾" = "∾𝕩∾";" ⋄ t}
    NewVar ⇐ {nvar +↩ 1 ⋄ "v_"∾𝕩∾"_"∾•Fmt nvar}
    Bind ⇐ {𝕊 n‿c: frames ↩ (¯1↓frames) ∾ <(¯1⊑frames) ∾ <n‿c ⋄ @}
    Push ⇐ {𝕤 ⋄ frames ∾↩ <⟨⟩ ⋄ @}
    Pop ⇐ {𝕤 ⋄ frames ↩ ¯1↓frames ⋄ @}
    Lookup ⇐ {   # innermost binding of name 𝕩 in this function, or ""
      all ← ∾frames
      i ← ⊑ (⌽⊑¨all) ⊐ <𝕩
      {i < ≠all ? 1⊑(¯1-i)⊑all ; ""}
    }
    Capture ⇐ {𝕊 n‿outer:
      i ← ⊑ (⊑¨cs) ⊐ <n
      cs ∾↩ (i=≠cs) / ⟨n‿outer⟩
      "e["∾(•Fmt i)∾"]"
    }
    Caps ⇐ {𝕤 ⋄ cs}
  }
  none ← {kind⇐"none"}

  # name → ⟨"c", C expression⟩ or ⟨"g", global info⟩
  Resolve ← {fc 𝕊 n:
    l ← fc.Lookup n
    {
      0 < ≠l ? ⟨"c", l⟩ ;
      "none" ≡ fc.parent.kind ? {IsGlobal n ? ⟨"g", GlobalInfo n⟩ ; ("undefined name "∾n) ! 0} ;
      r ← fc.parent Resolve n
      {"g" ≡ ⊑r ? r ; ⟨"c", fc.Capture n‿(1⊑r)⟩}
    }
  }

  Spec ← {fc 𝕊 s:
    {
      s ≡ "𝕩" ? "x" ;
      s ≡ "𝕨" ? "w" ;
      (s≡"𝕗") ∨ s≡"𝔽" ? "e[0]" ;
      (s≡"𝕘") ∨ s≡"𝔾" ? "e[1]" ;
      (s≡"𝕊") ∨ s≡"𝕤" ? SelfVal fc ;
      ("unsupported special name "∾s) ! 0
    }
  }
  SelfVal ← {𝕊 fc:
    k ← fc.fkind
    {
      k ≡ "fn" ? "g_"∾2↓fc.cname ;
      k ≡ "m1" ? fc.Tmp "mk_fn("∾fc.cname∾", 1, e[0])" ;
      k ≡ "m2" ? fc.Tmp "mk_fn("∾fc.cname∾", 2, e[0], e[1])" ;
      "𝕤 and 𝕊 as values are not supported in local blocks" ! 0
    }
  }

  Val ← {   # C expression for the value of a node
    fc 𝕊 node: "num" ≡ ⊑node ? "N("∾(CNum 1⊑node)∾")" ;
    fc 𝕊 node: "chr" ≡ ⊑node ? "C("∾(•Fmt (1⊑node)-@)∾")" ;
    fc 𝕊 node: "str" ≡ ⊑node ? Str 1⊑node ;
    fc 𝕊 node: "list" ≡ ⊑node ?
      items ← fc⊸Val¨ 1⊑node
      {0 = ≠items ? "mk_list(0, NULL)" ; fc.Tmp "mk_list("∾(•Fmt ≠items)∾", "∾(Ops items)∾")"} ;
    fc 𝕊 node: "var" ≡ ⊑node ?
      r ← fc Resolve 1⊑node
      {
        "c" ≡ ⊑r ? 1⊑r ;
        "fn" ≡ 1⊑1⊑r ? "g_"∾⊑1⊑r ;
        ("modifier "∾(⊑1⊑r)∾" used as a value") ! 0
      } ;
    fc 𝕊 node: "spec" ≡ ⊑node ? fc Spec 1⊑node ;
    fc 𝕊 node: "field" ≡ ⊑node ?
      "b.x only: no other namespaces" ! "b" ≡ 1⊑1⊑node
      BVal 2⊑node ;
    fc 𝕊 node: "call1" ≡ ⊑node ? fc Apply ⟨1⊑node, "NONE", fc Val 2⊑node⟩ ;
    fc 𝕊 node: "call2" ≡ ⊑node ? x ← fc Val 3⊑node ⋄ fc Apply ⟨1⊑node, fc Val 2⊑node, x⟩ ;
    fc 𝕊 node: "assign" ≡ ⊑node ? r ← fc Val 3⊑node ⋄ fc BindPat (2⊑node)‿r ⋄ r ;
    fc 𝕊 node: (⊑node) In "prim"‿"mod1"‿"mod2"‿"atop"‿"fork"‿"block" ? fc Derived node ;
    fc 𝕊 node: ("cannot compile "∾⊑node) ! 0
  }

  CallV ← {fc 𝕊 f‿w‿x: fc.Tmp "call("∾(Args f‿w‿x)∾")"}
  Simple ← {(⊑𝕩) In "var"‿"field"‿"spec"‿"prim"}   # applying it emits one call at most
  Direct ← {fc 𝕊 name‿env‿w‿x: fc.Tmp name∾"("∾(Args env‿w‿x)∾")"}

  # Apply a function node to C arguments w (or "NONE") and x
  Apply ← {
    fc 𝕊 node‿w‿x: "var" ≡ ⊑node ?
      r ← fc Resolve 1⊑node
      {
        "c" ≡ ⊑r ? fc CallV (1⊑r)‿w‿x ;
        "fn" ≡ 1⊑1⊑r ? fc Direct (2⊑1⊑r)‿"NULL"‿w‿x ;
        fc CallV (fc Val node)‿w‿x
      } ;
    fc 𝕊 node‿w‿x: "field" ≡ ⊑node ? fc.Tmp "b_"∾(2⊑node)∾"("∾(Args w‿x)∾")" ;
    fc 𝕊 node‿w‿x: ⟨"spec", "𝕊"⟩ ≡ node ?
      fc Direct fc.cname‿((fc.fkind In "fn"‿"imm1"‿"imm2") ⊑ "e"‿"NULL")‿w‿x ;
    fc 𝕊 node‿w‿x: "spec" ≡ ⊑node ? fc CallV (fc Spec 1⊑node)‿w‿x ;
    fc 𝕊 node‿w‿x: "prim" ≡ ⊑node ?
      c ← 1⊑node
      {
        c = '⊢' ? x ;
        c = '⊣' ? ("NONE"≡w) ⊑ w‿x ;
        c = '!' ? fc.Tmp "p_assert("∾(Args w‿x)∾")" ;
        fc CallV (fc Val node)‿w‿x
      } ;
    fc 𝕊 node‿w‿x: (⊑node) In "num"‿"chr"‿"str"‿"list" ? fc Val node ;   # data applied is itself
    fc 𝕊 node‿w‿x: "atop" ≡ ⊑node ? fc Apply ⟨1⊑node, "NONE", fc Apply ⟨2⊑node, w, x⟩⟩ ;
    fc 𝕊 node‿w‿x: "fork" ≡ ⊑node ?
      r ← fc Apply ⟨3⊑node, w, x⟩
      l ← fc Apply ⟨1⊑node, w, x⟩
      fc Apply ⟨2⊑node, l, r⟩ ;
    fc 𝕊 node‿w‿x: "mod1" ≡ ⊑node ?
      m ← 1⊑node ⋄ f ← 2⊑node
      {
        m ≡ ⟨"prim", '˜'⟩ ? fc Apply ⟨f, x, ("NONE"≡w) ⊑ w‿x⟩ ;
        m ≡ ⟨"prim", '˙'⟩ ? fc Val f ;
        "field" ≡ ⊑m ? fc.Tmp "bm_"∾(2⊑m)∾"("∾(Args (fc Val f)‿w‿x)∾")" ;
        (m ≡ ⟨"spec", "_𝕣"⟩) ∧ "m1" ≡ fc.fkind ? fc Direct fc.cname‿(Ops ⟨fc Val f⟩)‿w‿x ;
        "var" ≡ ⊑m ?
          g ← GlobalInfo 1⊑m
          {"m1d" ≡ 1⊑g ? fc Direct (2⊑g)‿(Ops ⟨fc Val f⟩)‿w‿x ; fc CallV (fc Derived node)‿w‿x} ;
        fc CallV (fc Derived node)‿w‿x
      } ;
    fc 𝕊 node‿w‿x: "mod2" ≡ ⊑node ?
      m ← 1⊑node ⋄ f ← 2⊑node ⋄ g ← 3⊑node
      AG ← {fc Apply ⟨g, 𝕨, 𝕩⟩}
      AF ← {fc Apply ⟨f, 𝕨, 𝕩⟩}
      {
        m ≡ ⟨"prim", '∘'⟩ ? "NONE" AF w AG x ;
        # 𝕨 F○G 𝕩 applies G twice: a simple G is called twice, anything
        # else is evaluated once as a value
        (m ≡ ⟨"prim", '○'⟩) ∧ ("NONE"≡w) ∨ Simple g ? gx ← "NONE" AG x ⋄ ("NONE"≡w) ◶ ⟨{𝕤⋄("NONE" AG w) AF gx}, {𝕤⋄"NONE" AF gx}⟩ @ ;
        m ≡ ⟨"prim", '○'⟩ ? gv ← fc Val g ⋄ gx ← fc CallV gv‿"NONE"‿x ⋄ (fc CallV gv‿"NONE"‿w) AF gx ;
        m ≡ ⟨"prim", '⊸'⟩ ? l ← "NONE" AF ("NONE"≡w) ⊑ w‿x ⋄ l AG x ;
        m ≡ ⟨"prim", '⟜'⟩ ? r ← "NONE" AG x ⋄ (("NONE"≡w) ⊑ w‿x) AF r ;
        m ≡ ⟨"prim", '⊘'⟩ ? ("NONE"≡w) ◶ ⟨{𝕤⋄w AG x}, {𝕤⋄"NONE" AF x}⟩ @ ;
        (m ≡ ⟨"spec", "_𝕣_"⟩) ∧ "m2" ≡ fc.fkind ? fc Direct fc.cname‿(Ops ⟨fc Val f, fc Val g⟩)‿w‿x ;
        "var" ≡ ⊑m ?
          gi ← GlobalInfo 1⊑m
          {"m2d" ≡ 1⊑gi ? fc Direct (2⊑gi)‿(Ops ⟨fc Val f, fc Val g⟩)‿w‿x ; fc CallV (fc Derived node)‿w‿x} ;
        fc CallV (fc Derived node)‿w‿x
      } ;
    fc 𝕊 node‿w‿x: fc CallV (fc Val node)‿w‿x
  }

  Mk ← {fc 𝕊 name‿os: fc.Tmp "mk_fn("∾name∾", "∾(•Fmt ≠os)∾(∾", "⊸∾¨os)∾")"}

  # Runtime objects for derived functions and blocks
  Derived ← {
    fc 𝕊 node: "prim" ≡ ⊑node ? PrimC 1⊑node ;
    fc 𝕊 node: "atop" ≡ ⊑node ? fc Mk "D_atop"‿(fc⊸Val¨ 1↓node) ;
    fc 𝕊 node: "fork" ≡ ⊑node ? fc Mk "D_fork"‿(fc⊸Val¨ 1↓node) ;
    fc 𝕊 node: "mod1" ≡ ⊑node ?
      m ← 1⊑node ⋄ f ← fc Val 2⊑node
      {
        "prim" ≡ ⊑m ? fc Mk (PrimC 1⊑m)‿⟨f⟩ ;
        "field" ≡ ⊑m ? fc Mk (BMod 2⊑m)‿⟨f⟩ ;
        (m ≡ ⟨"spec", "_𝕣"⟩) ∧ "m1" ≡ fc.fkind ? fc Mk fc.cname‿⟨f⟩ ;
        "var" ≡ ⊑m ?
          g ← GlobalInfo 1⊑m
          {
            "m1d" ≡ 1⊑g ? fc Mk (2⊑g)‿⟨f⟩ ;
            "m1i" ≡ 1⊑g ? fc.Tmp (2⊑g)∾"("∾f∾")" ;
            ("not a 1-modifier: "∾1⊑m) ! 0
          } ;
        "unsupported 1-modifier" ! 0
      } ;
    fc 𝕊 node: "mod2" ≡ ⊑node ?
      m ← 1⊑node ⋄ g ← fc Val 3⊑node ⋄ f ← fc Val 2⊑node
      {
        "prim" ≡ ⊑m ? fc Mk ⟨PrimC 1⊑m, f‿g⟩ ;
        (m ≡ ⟨"spec", "_𝕣_"⟩) ∧ "m2" ≡ fc.fkind ? fc Mk ⟨fc.cname, f‿g⟩ ;
        "var" ≡ ⊑m ?
          gi ← GlobalInfo 1⊑m
          {
            "m2d" ≡ 1⊑gi ? fc Mk ⟨2⊑gi, f‿g⟩ ;
            "m2i" ≡ 1⊑gi ? fc.Tmp (2⊑gi)∾"("∾(Args f‿g)∾")" ;
            ("not a 2-modifier: "∾1⊑m) ! 0
          } ;
        "unsupported 2-modifier" ! 0
      } ;
    fc 𝕊 node: "block" ≡ ⊑node ?
      "only function blocks can be local" ! "fn" ≡ 1⊑node
      nlocal +↩ 1 ⋄ name ← "L_"∾•Fmt nlocal
      lfc ← NewFC fc‿"local"‿name
      lfc Bodies 3⊑node
      fc Mk name‿(1⊑¨lfc.Caps @) ;
    fc 𝕊 node: ("cannot make a value of "∾⊑node) ! 0
  }

  BindPat ← {
    fc 𝕊 pat‿c: "var" ≡ ⊑pat ?
      v ← fc.NewVar 1⊑pat
      fc.Emit "  B "∾v∾" = "∾c∾";"
      fc.Bind (1⊑pat)‿v ;
    fc 𝕊 pat‿c: "list" ≡ ⊑pat ?
      items ← 1⊑pat
      fc.Emit "  need_list("∾c∾", "∾(•Fmt ≠items)∾");"
      (↕≠items) {fc BindPat 𝕩‿(fc.Tmp "list_get("∾c∾", "∾(•Fmt 𝕨)∾")")}¨ items
      @ ;
    fc 𝕊 pat‿c: ("cannot assign to "∾⊑pat) ! 0
  }

  # Bodies: valence and header checks, predicates, statements
  Bodies ← {fc 𝕊 bodies:
    n ← ≠bodies
    hdrs ← ⊑¨bodies ⋄ stmts ← 1⊑¨bodies
    preds ← {∨´ ("pred"≡⊑)¨ 𝕩}¨ stmts
    uncond ← (0=≠¨hdrs) ∧ ¬preds         # plain headerless bodies come last
    "headerless bodies must come last" ! ∧´ (∨`uncond) ≤ uncond
    "at most two headerless bodies" ! 2 ≥ +´uncond
    two ← 2 = +´uncond
    Valence ← {
      𝕊 h‿i: 0 < ≠h ? w‿x ← 1‿2⊏h ⋄ (0<≠w) ⊑ ⟨(0<≠x) ⊑ "any"‿"mon", "dy"⟩ ;
      𝕊 h‿i: two ∧ i⊑uncond ? (i = n-2) ⊑ "dy"‿"mon" ;
      𝕊 h‿i: "any"
    }
    vals ← Valence¨ hdrs ⋈¨ ↕n
    {𝕊 i:
      next ← "b"∾•Fmt i+1
      fc.Emit "  b"∾(•Fmt i)∾":; {"
      v ← i⊑vals
      fc.Emit⍟("mon"≡v) "  if (!is_none(w)) goto "∾next∾";"
      fc.Emit⍟("dy"≡v) "  if (is_none(w)) goto "∾next∾";"
      fc.Push @
      h ← i⊑hdrs
      {𝕤
        hw‿hx‿hf‿hg ← 1↓h
        BindArg ← {
          𝕊 p‿c: "spec" ≡ ⊑p ? @ ;
          𝕊 p‿c: "var" ≡ ⊑p ? fc.Bind (1⊑p)‿c ;
          𝕊 p‿c: "header patterns other than names are not supported" ! 0
        }
        BindArg¨ (0<≠¨hw‿hx‿hf‿hg) / ⟨hw‿"w", hx‿"x", hf‿"e[0]", hg‿"e[1]"⟩
      }⍟(0<≠h) @
      st ← i⊑stmts
      last ← {𝕊 k‿e:
        c ← fc Val e
        fc.Emit⍟("pred"≡k) "  if (!truth("∾c∾")) goto "∾next∾";"
        c
      }¨ st
      "a body can't end in a predicate" ! "expr" ≡ ⊑¯1⊑st
      fc.Emit "  return "∾(¯1⊑last)∾";"
      fc.Emit "  }"
      fc.Pop @
    }¨ ↕n
    fc.Emit "  b"∾(•Fmt n)∾":; return vm_nomatch();"
    Finish fc
  }
  Finish ← {𝕊 fc:
    k ← fc.fkind
    sig ← {
      k In "fn"‿"m1"‿"m2"‿"local" ? "static B "∾fc.cname∾"(B *e, B w, B x)" ;
      k ≡ "imm1" ? "static B "∾fc.cname∾"(B f0)" ;
      "static B "∾fc.cname∾"(B f0, B g0)"
    }
    pre ← {
      k ≡ "imm1" ? "  B e[1] = {f0};" ;
      k ≡ "imm2" ? "  B e[2] = {f0, g0};" ;
      "  (void)e; (void)w; (void)x;"
    }
    protos ∾↩ <sig∾";"
    defs ∾↩ <Lines ⟨sig∾" {", pre⟩ ∾ (fc.Lines @) ∾ ⟨"}", ""⟩
    @
  }

  # Top-level statements
  Top ← {𝕊 node:
    "top level: only definitions" ! "assign" ≡ ⊑node
    arrow‿lhs‿rhs ← 1↓node
    "top level: define names only" ! "var" ≡ ⊑lhs
    name ← 1⊑lhs
    {
      "sys" ≡ ⊑rhs ? globals ∾↩ <name‿"b"‿"" ;
      "block" ≡ ⊑rhs ?
        type‿deferred ← 1‿2⊏rhs
        {
          type ≡ "fn" ?
            globals ∾↩ <name‿"fn"‿("F_"∾name)
            inits ∾↩ <"  g_"∾name∾" = fn_static(F_"∾name∾");"
            exports ∾↩ (arrow='⇐') / ⟨name⟩
            (NewFC none‿"fn"‿("F_"∾name)) Bodies 3⊑rhs ;
          type ≡ "imm" ? "immediate blocks at top level are not supported" ! 0 ;
          deferred ?
            globals ∾↩ <name‿(type∾"d")‿("M_"∾name)
            (NewFC none‿type‿("M_"∾name)) Bodies 3⊑rhs ;
          globals ∾↩ <name‿(type∾"i")‿("MI_"∾name)
          fc ← NewFC none‿("imm"∾1↓type)‿("MI_"∾name)
          "an immediate modifier has one body" ! 1 = ≠3⊑rhs
          "an immediate modifier has one statement" ! 1 = ≠1⊑⊑3⊑rhs
          r ← fc Val 1⊑⊑1⊑⊑3⊑rhs
          fc.Emit "  return "∾r∾";"
          Finish fc
        } ;
      "top level: definitions must be blocks for now" ! 0
    }
  }
  Top¨ prog

  fns ← ("fn" ≡ 1⊸⊑)¨⊸/ globals
  StrInit ← {"  S"∾(•Fmt 𝕨)∾" = str_lit((const uint32_t[]){"∾(∾(•Fmt¨ 𝕩-@)∾¨<", ")∾"0}, "∾(•Fmt ≠𝕩)∾");"}
  Lines ∾⟨
    ⟨"// Generated by src/c.bqn. Do not edit.", ""⟩
    {"static B g_"∾(⊑𝕩)∾";"}¨ fns
    {"static B S"∾(•Fmt 𝕩)∾";"}¨ ↕≠strs
    {"static B BV_"∾𝕩∾";"}¨ bvals
    {"static B BF_"∾𝕩∾"(B *e, B w, B x) { (void)e; return b_"∾𝕩∾"(w, x); }"}¨ bvals
    {"static B BM_"∾𝕩∾"(B *e, B w, B x) { return bm_"∾𝕩∾"(e[0], w, x); }"}¨ bmods
    protos ∾ ⟨""⟩
    defs
    ⟨"static void gen_init(void) {"⟩
    (↕≠strs) StrInit¨ strs
    {"  BV_"∾𝕩∾" = fn_static(BF_"∾𝕩∾");"}¨ bvals
    inits
    ⟨"}", "", "static const struct { const char *name; B *val; } gen_exports[] = {"⟩
    {"  {"""∾𝕩∾""", &g_"∾𝕩∾"},"}¨ exports
    ⟨"  {0, 0}", "};"⟩
  ⟩
}

Compile ⇐ {Gen Parse Lex d.Check 𝕩}
