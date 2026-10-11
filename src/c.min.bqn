# c.min.bqn: the compiler of c.bqn, written data-parallel in the style of
# Co-dfns. It produces the same C.
#
# The program is held as columns: one entry per token, then one per node.
# Passes work on whole columns with scans, grouping, sorting and selection,
# instead of walking a tree. A tree is a parent column; order among siblings
# is a slot column. The few loops run once per nesting level, as fixpoints.
#
#   Lex src        → kind‿text‿line columns
#   Parse columns  → node table (see Parse)
#   Gen table      → C source
#   Compile src    → Gen Parse Lex dialect.Check src

d ← •Import "dialect.bqn"

nl ← @+10
letters ← ('a'+↕26)∾'A'+↕26
digits ← '0'+↕10
specChars ← "𝕨𝕩𝕗𝕘𝕤𝕎𝕏𝔽𝔾𝕊𝕣"
puncts ← "(){}⟨⟩[]‿;:?←⇐↩.·"
primChars ← "∘○⊸⟜˜˙⊘◶⍟⊢⊣!"

# Segments: 𝕨 marks the start of each segment of 𝕩
SegSum ← {(+`𝕩) - ⌈` 𝕨 × (+`𝕩) - 𝕩}                 # scan +` within segments
Starts ← {(≠𝕩) ↑ 1 ∾ (1↓𝕩) ≢¨ ¯1↓𝕩}                        # starts of runs of equal keys

# ---- lexing
#
# Strings, characters and comments are found by a scan over a state table.
# States: 0 code, 1 in a string, 2 in a comment, 3 after ', 4 after 'c.
# Classes: 0 other, 1 ", 2 #, 3 ', 4 newline.
lexT ← ⟨0‿1‿2‿3‿0, 1‿0‿1‿1‿1, 2‿2‿2‿2‿0, 4‿4‿4‿4‿4, 0‿0‿0‿0‿0⟩
kindNames ← "str"‿"chr"‿"num"‿"sys"‿"spec"‿"name"‿"sep"‿"p"‿"prim"

Lex ⇐ {
  s ← 𝕩
  st ← 0 {𝕩⊑𝕨⊑lexT}` (s='"') + (2×s='#') + (3×s=''') + 4×s=nl
  bf ← »st                                     # state before each character
  reopen ← (bf=0) ∧ (st=1) ∧ »(bf=1)∧st=0      # second quote of ""
  sstart ← (bf=0) ∧ (st=1) ∧ ¬reopen
  cstart ← (bf=0) ∧ st=3
  code ← ((bf=0) ∧ st=0) ∨ (s=nl) ∧ bf∊0‿2
  lit ← (st∊1‿3‿4) ∨ bf∊1‿3‿4
  isd ← s∊digits
  word ← code ∧ (s∊letters∾digits∾"_¯∞π•𝕣") ∨ (s='.') ∧ (»isd) ∧ «isd
  ws ← s∊" "∾@+9
  start ← (code ∧ (¬ws) ∧ ¬word ∧ »word) ∨ sstart ∨ cstart
  # quotes that aren't part of a literal's value: openers, closers, and the
  # second quote of each ""
  closeEnd ← (bf=1) ∧ (st=0) ∧ ¬«reopen
  quote ← sstart ∨ reopen ∨ closeEnd ∨ cstart ∨ bf=4
  keep ← ((code ∧ ¬ws) ∨ lit) ∧ ¬quote
  id ← ¯1 + +`start
  nt ← +´start
  texts ← ((keep/id) ∾ nt) ⊔ keep/s
  line ← start / 1 + +`»s=nl
  c0 ← start / s                               # first character, quotes included
  w0 ← (start/word)
  m ← > ⟨
    c0='"', (c0=''') ∨ c0='@', w0 ∧ c0∊digits∾"¯∞π", c0='•'
    (c0∊specChars) ∨ texts∊"_𝕣"‿"_𝕣_", w0 ∧ c0∊letters∾"_"
    c0∊nl∾"⋄,", c0∊puncts, c0∊primChars, 1¨c0
  ⟩
  kind ← +˝ ∧` ¬m                              # index of the first class that fits
  "unexpected character" ! ∧´ kind < 9
  kind ↩ kind ⊏ kindNames
  # one-character tokens hold the character itself; @ is the null character
  text ← (kind ∊ "chr"‿"sep"‿"p"‿"prim") {𝕨 ? ⊑𝕩 ; 𝕩}¨ texts
  text ↩ @¨⌾((c0='@')⊸/) text
  kind‿text‿line
}

# ---- parsing
#
# Parse kind‿text‿line → ty‿a1‿a2‿par‿slot: one entry per node, holding its
# type and values (as in c.bqn's nested nodes), its parent, and its position
# among the parent's children. Node 0 is the program; any other node with
# parent ¯1 is unused (parentheses, once spliced out).
#
#   1. Each token's container (enclosing bracket) comes from a bins lookup.
#   2. In each container, separators split segments, and arrows split each
#      segment into units. A unit is one expression; units are contiguous.
#   3. A unit's terms are its tokens glued by . and ‿.
#   4. Roles come from spelling. A parenthesis or an assignment has the role
#      of its unit: a fixpoint over nesting.
#   5. Modifiers bind by a shift; then application and trains by scans, for
#      all units at once.

Norm ← {(𝕩≠'_') / 𝕩 + 32×(𝕩≥'A')∧𝕩≤'Z'}
Role ← {
  𝕊 s: ('_'=⊑s) ∧ ('_'=¯1⊑s) ∧ 1<≠s ? "m2" ;
  𝕊 s: '_'=⊑s ? "m1" ;
  𝕊 s: ∨´(⊑s) = 'A'+↕26 ? "f" ;
  𝕊 s: "s"
}
SpecRole ← {𝕩≡"_𝕣" ? "m1" ; 𝕩≡"_𝕣_" ? "m2" ; ∨´(⊑𝕩)="𝕎𝕏𝔽𝔾𝕊" ? "f" ; "s"}
PrimRole ← {∨´𝕩="⊢⊣!" ? "f" ; ∨´𝕩="˜˙" ? "m1" ; "m2"}
_fix ← {𝔽 _𝕣⍟(𝕩≢⊢) 𝔽 𝕩}            # apply 𝔽 until nothing changes
Rank ← {¯1 + +`𝕩}                    # rank of each marked position
Is ← {𝕩 ≡¨ <𝕨}                       # "str" Is list

Parse ⇐ {𝕊 kd‿tx‿ln:
  n ← ≠kd
  IsP ← {("p" Is kd) ∧ tx ∊ 𝕩}

  # -- 1. containers
  op ← IsP "({⟨" ⋄ cl ← IsP ")}⟩"
  lvl ← (+`op-cl) - op
  "unbalanced brackets" ! (∧´ lvl ≥ 0) ∧ 0 = +´op-cl
  oi ← /op ⋄ oc ← oi + (n+1) × oi⊏lvl
  so ← ⍋oc
  enc ← ((so⊏oi) ∾ n) ⊏˜ 0 ⌈ ¯1 + (so⊏oc) ⍋ (↕n) + (n+1) × lvl-1
  ctr ← n + (lvl>0) × enc - n          # container of each token; n is the top
  cpar ← ctr ∾ n                       # container of each container
  cch ← tx ∾ <'r'                       # its bracket, 'r' at the top

  # -- 2. segments and units, with tokens inode container order
  perm ← {𝕩 ⊏˜ ⍋ 𝕩⊏ctr} (¬cl)/↕n
  c ← perm⊏ctr ⋄ g0 ← Starts c
  sep ← perm ⊏ ("sep" Is kd) ∨ IsP ";:?"
  semi ← perm ⊏ IsP ";"
  sid ← (g0 SegSum sep) - sep          # a separator ends its segment
  bid ← (g0 SegSum semi) - semi        # body within a block
  arw ← perm ⊏ IsP "←⇐↩"
  al ← (g0 ∨ »sep) SegSum arw          # arrow level within the segment
  skey ← sid + (n+1) × c
  sch ← (perm ⊏ "sep" Is kd) {𝕨 ? 's' ; 𝕩}¨ perm⊏tx
  send ← ((sep/sch) ∾ 'e') ⊏˜ (sep/skey) ⊐ skey     # how each segment ends
  tp ← /¬sep ∨ arw                     # positions of term tokens
  tt ← tp⊏perm                         # their tokens
  ust ← Starts (tp⊏al) + (n+1) × tp⊏skey
  uid ← Rank ust ⋄ nu ← +´ust
  U ← {ust / tp ⊏ 𝕩}                   # per position → per unit
  uc ← U c ⋄ ual ← U al ⋄ uend ← U send ⋄ ubid ← U bid
  uarrow ← (perm⊏tx) ⊏˜ ¯1 + ust/tp     # the arrow before a unit at level > 0
  uhdr ← (uend = ':') ∧ ual = 0
  "an assignment needs a target" ! ∧´ (ual>0) ≤ (»ual) = ual-1

  # -- 3. leaves, fields and terms
  dot ← tt⊏IsP "." ⋄ tie ← tt⊏IsP "‿"
  fglue ← (¬ust) ∧ dot ∨ »dot
  fgs ← (¬fglue) ∧ ¬tie                # field group starts
  tgs ← ¬fglue ∨ (¬ust) ∧ tie ∨ »tie   # term starts
  atom ← ¬dot ∨ tie ∨ (¬ust) ∧ »dot
  lt ← atom/tt ⋄ nl0 ← ≠lt
  lk ← lt⊏kd ⋄ lx ← lt⊏tx
  lty ← lk {𝕨≡"name" ? "var" ; 𝕨≡"p" ? (⊑"·(⟨{" ⊐ 𝕩) ⊑ "nothing"‿"paren"‿"list"‿"block" ; 𝕨}¨ lx
  lid ← 1 + Rank atom                  # leaf node of each atom token
  fi ← /fgs                            # first token of each field group
  "one level of field access only" ! ¬∨´ dot ∧ »»dot
  hasf ← fi ⊏ «dot
  nf ← +´hasf ⋄ f0 ← 1+nl0
  fnm ← (hasf/fi+2) ⊏ tt⊏tx             # field names
  gnode ← (fi⊏lid) + hasf × (f0 + Rank hasf) - fi⊏lid
  tgr ← ((/fgs) ⊏ Rank tgs) ⊔ ↕≠fi     # field groups of each term
  isstr ← 1 < ≠¨tgr ⋄ ns ← +´isstr ⋄ s0 ← f0+nf
  tf ← ⊑¨tgr
  tnode ← (tf⊏gnode) + isstr × (s0 + Rank isstr) - tf⊏gnode
  tunit ← (/tgs) ⊏ uid
  ntm ← ≠tf
  tleaf ← (tf⊏fi) ⊏ lid-1              # leaf index of each term's first atom
  rel ← ⟨⟨hasf/fi⊏lid, f0+↕nf, nf⥊1⟩⟩  # child‿parent‿slot
  AddRel ← {rel ∾↩ <𝕩 ⋄ @}
  AddRel ⟨(∾isstr/tgr) ⊏ gnode, s0 + /≠¨isstr/tgr, ∾ ↕∘≠¨ isstr/tgr⟩

  # -- blocks: type from the special names used directly, and the headers
  bl ← /"block" Is lty ⋄ btok ← bl⊏lt
  spl ← /"spec" Is lty
  sblk ← {𝕩 + (¬(𝕩⊏cch) ∊ "{r") × (𝕩⊏cpar) - 𝕩} _fix (spl⊏lt)⊏ctr
  stxt ← spl⊏lx
  hu ← /uhdr                           # header units
  hselfT ← {
    ts ← /(tunit = 𝕩) ∧ (¬isstr) ∧ ("spec" Is tleaf⊏lty) ∧ (tleaf⊏lx) ∊ "𝕊"‿"_𝕣"‿"_𝕣_"
    "header needs 𝕊, _𝕣 or _𝕣_" ! 1 ≤ ≠ts
    ⊑ts
  }¨ hu                                # the self term of each header
  hkind ← (⊑"𝕊"‿"_𝕣"‿"_𝕣_" ⊐ <)¨ (hselfT⊏tleaf) ⊏ lx
  hkind ↩ hkind ⊏ "fn"‿"m1"‿"m2"
  binfo ← {
    used ← (sblk = 𝕩) / stxt ⋄ hk ← (𝕩 = hu⊏uc) / hkind
    A ← {∨´ 𝕩 ∊ used}
    t ← {
      (⊑(<"m2")∊hk) ∨ A "𝔾"‿"𝕘"‿"_𝕣_" ? "m2" ;
      (⊑(<"m1")∊hk) ∨ A "𝔽"‿"𝕗"‿"_𝕣" ? "m1" ;
      (⊑(<"fn")∊hk) ∨ A "𝕨"‿"𝕩"‿"𝕤"‿"𝕊"‿"𝕎"‿"𝕏" ? "fn" ;
      "imm"
    }
    t ⋈ (0<≠hk) ∨ A "𝕨"‿"𝕩"‿"𝕤"‿"𝕊"
  }¨ btok
  btype ← ⊑¨binfo ⋄ bdef ← 1⊑¨binfo

  # -- 4. roles
  lrole ← lty {𝕨≡"var" ? Role 𝕩 ; 𝕨≡"spec" ? SpecRole 𝕩 ; 𝕨≡"prim" ? PrimRole 𝕩 ; "s"}¨ lx
  lrole ↩ (((⊑"fn"‿"m1"‿"m2"‿"imm" ⊐ <)¨ btype) ⊏ "f"‿"m1"‿"m2"‿"s")⌾(bl⊸⊏) lrole
  grole ← (Role¨ fnm)⌾(hasf⊸/) (fi⊏lid-1) ⊏ lrole     # role of each field group
  trole ← "s"¨⌾(isstr⊸/) tf ⊏ grole                   # role of each term
  ufirst ← tunit ⊐ ↕nu ⋄ ulast ← ¯1 + 1↓ufirst ∾ ntm
  # assignments: the last term of the unit before becomes the assignment
  au ← /ual>0 ⋄ na ← ≠au ⋄ a0 ← s0+ns
  lhsT ← ¯1 + au⊏ufirst
  "an assignment needs a target" ! ∧´ (au-1) = lhsT⊏tunit
  # parentheses: a term that is one paren leaf; its unit is the first inode it
  pT ← /(¬isstr) ∧ (¬tf⊏hasf) ∧ "paren" Is tleaf⊏lty
  pu ← uc ⊐ (pT⊏tleaf)⊏lt
  URole ← {   # role of each unit, from its terms' roles 𝕩
    lr ← ulast⊏𝕩 ⋄ pr ← (0⌈ulast-1)⊏𝕩
    "f"¨⌾(((ufirst < ulast) ∧ ("m1" Is lr) ∨ "m2" Is pr)⊸/) lr
  }
  tr ← {r ← URole 𝕩 ⋄ (au⊏r)⌾(lhsT⊸⊏) (pu⊏r)⌾(pT⊸⊏) 𝕩} _fix trole
  AddRel ⟨lhsT ⊏ tnode, a0+↕na, na⥊2⟩
  tnode ↩ (a0+↕na)⌾(lhsT⊸⊏) tnode

  # -- 5. reduction of every expression unit's terms
  em ← ¬tunit⊏uhdr
  en ← em/tnode ⋄ er ← em/tr ⋄ eu ← em/tunit
  eus ← Starts eu ⋄ eue ← (1↓eus) ∾ 1
  m2 ← "m2" Is er
  isM ← (("m1" Is er) ∨ m2) ∧ ¬eus ∧ eue    # modifiers, except a unit's only term
  "a modifier needs an operand on its left" ! ∧´ isM ≤ ¬eus
  "a 2-modifier needs an operand on its right" ! ∧´ (isM∧m2) ≤ ¬eue
  cons ← (»isM∧m2) ∧ ¬eus                   # right operand of a 2-modifier
  nm ← +´isM ⋄ m0 ← a0+na
  mnode ← m0 + Rank isM
  root ← (cons/»mnode)⌾(cons⊸/) (isM/mnode)⌾(isM⊸/) en
  AddRel ⟨isM/en, isM/mnode, nm⥊1⟩
  AddRel ⟨isM/»root, isM/mnode, nm⥊2⟩
  AddRel ⟨(isM∧m2)/«en, (isM∧m2)/mnode, (+´isM∧m2)⥊3⟩
  mty ← (isM/m2) ⊏ "mod1"‿"mod2"
  item ← (¬isM∧m2) ∧ eue ∨ ¬«isM            # last term of each operand span
  inode ← item/root ⋄ iu ← item/eu
  ir ← "f"¨⌾((item/isM∨cons)⊸/) item/er
  ius ← Starts iu ⋄ iue ← (1↓ius) ∾ 1
  urank ← Rank ius ⋄ ni ← ≠inode
  lastI ← urank ⊏ /iue                       # last item of each item's unit
  one ← ius ∧ iue                            # the only item of its unit
  isF ← "f" Is ir
  # application: a unit ending inode a subject
  app ← "s" Is lastI⊏ir
  "double subjects (missing ‿?)" ! ∧´ (app ∧ (¬isF) ∧ ¬iue) ≤ «isF
  cF ← app ∧ isF ⋄ nc ← +´cF ⋄ c0 ← m0+nm
  cnode ← c0 + Rank cF
  hasW ← cF ∧ (¬ius) ∧ »¬isF
  bb ← ni+2                                   # the next function to the right:
  key ← (urank×bb) + (cF×↕ni) + (¬cF)×bb-1     #   a suffix minimum, by unit
  nk ← 1 ↓ (⌊`⌾⌽ key) ∾ bb×ni+1
  hasN ← (urank = ⌊nk÷bb) ∧ (bb-1) > bb|nk
  xnode ← (lastI⊏inode) + hasN × (((ni-1) ⌊ bb|nk) ⊏ cnode) - lastI⊏inode
  AddRel ⟨cF/inode, cF/cnode, nc⥊1⟩
  AddRel ⟨hasW/»inode, hasW/cnode, (+´hasW)⥊2⟩
  AddRel ⟨cF/xnode, cF/cnode, cF/2+hasW⟩
  cty ← (cF/hasW) ⊏ "call1"‿"call2"
  # trains: a unit ending inode a function; forks at odd positions from the right
  r ← lastI - ↕ni
  odd ← ("f" Is lastI⊏ir) ∧ 2|r
  "a train needs functions inode odd positions from the right" ! ∧´ odd ≤ isF
  nt ← +´odd ⋄ r0 ← c0+nc
  rnode ← r0 + Rank odd
  isFork ← odd ∧ ¬ius
  hnode ← ((r=1) × «inode) + (r≠1) × ««rnode
  AddRel ⟨isFork/»inode, isFork/rnode, (+´isFork)⥊1⟩
  AddRel ⟨odd/inode, odd/rnode, odd/1+isFork⟩
  AddRel ⟨odd/hnode, odd/rnode, odd/2+isFork⟩
  rty ← (odd/isFork) ⊏ "atop"‿"fork"
  # the root of each unit: its first call, its leftmost fork, or its item
  cand ← cF ∨ odd ∨ one
  candN ← inode + (cF × cnode - inode) + odd × rnode - inode
  uroot ← ((cand/candN) ⊏˜ (cand/urank) ⊐ ↕+´ius)⌾((/¬uhdr)⊸⊏) nu⥊0
  # a parenthesis is replaced by its unit's root
  b0 ← r0+nt
  pnode ← 1 + pT⊏tleaf
  pmap ← {𝕩⊏𝕩} _fix (pu⊏uroot)⌾(pnode⊸⊏) ↕b0
  uroot ↩ uroot ⊏ pmap
  rel ↩ {⟨(⊑𝕩)⊏pmap⟩ ∾ 1↓𝕩}¨ rel
  AddRel ⟨au⊏uroot, a0+↕na, na⥊3⟩

  # -- containers: the program, lists, blocks with their bodies and headers
  pu0 ← /(uc = n) ∧ ual = 0
  "only statements at the top level" ! ∧´ ¬pu0⊏uhdr
  AddRel ⟨pu0⊏uroot, 0¨pu0, ↕≠pu0⟩
  InGroup ← {¯1 + (Starts 𝕩) SegSum 1¨𝕩}     # position within runs of equal keys
  ll ← /"list" Is lty
  lu ← /(ual = 0) ∧ uc ∊ ll⊏lt
  AddRel ⟨lu⊏uroot, 1 + ll ⊏˜ (ll⊏lt) ⊐ lu⊏uc, InGroup lu⊏uc⟩
  bu ← /(ual = 0) ∧ uc ∊ btok
  bkey ← (bu⊏ubid) + (n+1) × bu⊏uc
  bst ← Starts bkey ⋄ nb ← +´bst
  bnode ← b0 + Rank bst                      # body of each unit inode a block
  bodyU ← bst/bu
  AddRel ⟨b0+↕nb, 1 + bl ⊏˜ btok ⊐ bodyU⊏uc, InGroup bodyU⊏uc⟩
  su ← (¬bu⊏uhdr) / bu ⋄ st0 ← b0+nb
  AddRel ⟨st0+↕≠su, (bu⊐su)⊏bnode, InGroup (bu⊐su)⊏bnode⟩
  AddRel ⟨su⊏uroot, st0+↕≠su, (≠su)⥊1⟩
  h0 ← st0+≠su ⋄ nh ← ≠hu
  AddRel ⟨h0+↕nh, (bu⊐hu)⊏bnode, nh⥊¯1⟩
  hoff ← ((⊑"fn"‿"m1"‿"m2" ⊐ <)¨ hkind) ⊏ ⟨¯1‿1, ¯2‿1‿¯1, ¯2‿2‿¯1‿1⟩  # w x f g, from the self term
  ht ← hselfT + hoff
  hok ← ht {(𝕨 ≥ 𝕩⊏ufirst) ∧ 𝕨 ≤ 𝕩⊏ulast}¨ hu
  AddRel ⟨∾ hok /¨ ht ⊏¨ <tnode, ∾ hok /¨ (≠¨ht) ⥊¨ h0+↕nh, ∾ hok /¨ (1+↕∘≠)¨ ht⟩

  # -- the table
  nnode ← h0+nh
  la1 ← btype⌾(bl⊸⊏) lty {𝕨≡"var" ? Norm 𝕩 ; 𝕩}¨ lx
  la2 ← bdef⌾(bl⊸⊏) lx
  e ← <⟨⟩
  ty ← ⟨"program"⟩ ∾ lty ∾ (nf⥊<"field") ∾ (ns⥊<"list") ∾ (na⥊<"assign") ∾ mty ∾ cty ∾ rty ∾ (nb⥊<"body") ∾ ((≠su)⥊<"stmt") ∾ nh⥊<"header"
  a1 ← e ∾ la1 ∾ (Norm¨ fnm) ∾ (ns⥊e) ∾ (au⊏uarrow) ∾ ((nm+nc+nt+nb)⥊e) ∾ (((su⊏uend)='?') ⊏ "expr"‿"pred") ∾ hkind
  a2 ← e ∾ la2 ∾ fnm ∾ (nnode-1+nl0+nf)⥊e
  cs‿ps‿ss ← ∾¨ <˘⍉> rel
  dup ← ⍷ (¬∊cs)/cs
  ("a node with two parents: "∾•Fmt ⟨dup, dup⊏ty, {(/𝕩=cs)⊏ps}¨ dup⟩ ∾ ⟨{((/𝕩=cs)⊏ps)⊏ty}¨ dup⟩) ! 0=≠dup
  par ← ps⌾(cs⊸⊏) nnode⥊¯1
  slot ← ss⌾(cs⊸⊏) nnode⥊0
  ty‿a1‿a2‿par‿slot
}

# Nest table: the program as c.bqn's nested nodes, to check Parse
Nest ⇐ {𝕊 ty‿a1‿a2‿par‿slot:
  ch ← {𝕩 ⊏˜ ⍋ 𝕩⊏slot}¨ ((par ∾ ≠par) ⊔ ↕≠par)
  Nd ← {
    t ← 𝕩⊑ty ⋄ v ← 𝕩⊑a1 ⋄ k ← 𝕩⊑ch ⋄ i ← 𝕩
    {
      ⊑(<t) ∊ ⟨"num","str","sys","spec","chr","prim"⟩ ? ⟨t, v⟩ ;
      t ≡ "var" ? ⟨t, v, i⊑a2⟩ ;
      t ≡ "nothing" ? ⟨t⟩ ;
      t ≡ "field" ? ⟨t, Nd ⊑k, v, i⊑a2⟩ ;
      t ≡ "list" ? ⟨t, Nd¨ k⟩ ;
      t ≡ "assign" ? ⟨t, v⟩ ∾ Nd¨ k ;
      t ≡ "block" ? ⟨t, v, i⊑a2, Nd¨ k⟩ ;
      t ≡ "body" ? h ← ¯1 = k⊏slot ⋄ ⟨(∨´h) ◶ ⟨⟨⟩, {𝕤 ⋄ Nd ⊑h/k}⟩ @, Nd¨ (¬h)/k⟩ ;
      t ≡ "stmt" ? ⟨v, Nd ⊑k⟩ ;
      t ≡ "header" ? ⟨v⟩ ∾ {⊑𝕩 ∊ k⊏slot ? Nd (⊑(k⊏slot)⊐𝕩)⊑k ; ⟨⟩}¨ 1+↕4 ;
      ⟨t⟩ ∾ Nd¨ k
    }
  }
  Nd¨ 0⊑ch
}

# ---- C generation
#
# Gen table → C, the same text as c.bqn's Gen.
#
#   1. Usage, top down one level at a time: a rule table keyed by the
#      parent's mode and the child's slot gives each child its usage (value,
#      applied, pattern or structural), the sources of its arguments when it
#      is applied, and its evaluation rank among its siblings. Combinators
#      and trains applied on the spot are expanded here.
#   2. Lines: each node's own C lines come from templates; bodies and
#      functions add their framing.
#   3. Order: each line's key is its node's path of ranks. Sorting the keys
#      gives evaluation order, which numbers temporaries, variables, local
#      functions, strings and basis values.
#   4. Names: a binary search over the definitions before each use, and one
#      step out per enclosing function for captured names.

primNames ← "∘○⊸⟜˜˙⊘◶⍟⊢⊣!"
primCs ← "D_atop2"‿"D_over"‿"D_before"‿"D_after"‿"D_swap"‿"D_const"‿"D_valences"‿"D_choose"‿"D_repeat"‿"P_right"‿"P_left"‿"P_assert"

# Child rules: parent mode, child slot ("*" for any), child usage, sources
# of its arguments, rank. Usage V is a value and A an application; anything
# else names the child's mode directly. Sources: N none, w x the parent's
# arguments, wx the parent's 𝕨 or else 𝕩, s1 s2 s3 the sibling in that slot,
# l0 l1 the parent's own line. Rank * is the slot.
rules ← ⟨
  "prog"‿"*"‿"def"‿"N"‿"N"‿"*",   "def"‿"2"‿"skip"‿"N"‿"N"‿"0",   "def"‿"3"‿"top"‿"N"‿"N"‿"1"
  "fn"‿"*"‿"body"‿"N"‿"N"‿"*",    "dblock"‿"*"‿"body"‿"N"‿"N"‿"*", "imm"‿"*"‿"ibody"‿"N"‿"N"‿"*"
  "body"‿"¯1"‿"skip"‿"N"‿"N"‿"0", "body"‿"*"‿"stmt"‿"N"‿"N"‿"*",  "ibody"‿"*"‿"istmt"‿"N"‿"N"‿"*"
  "stmt"‿"1"‿"V"‿"N"‿"N"‿"0",     "istmt"‿"1"‿"V"‿"N"‿"N"‿"0"
  "list"‿"*"‿"V"‿"N"‿"N"‿"*"
  "call1"‿"2"‿"V"‿"N"‿"N"‿"0",    "call1"‿"1"‿"A"‿"N"‿"s2"‿"1"
  "call2"‿"3"‿"V"‿"N"‿"N"‿"0",    "call2"‿"2"‿"V"‿"N"‿"N"‿"1",    "call2"‿"1"‿"A"‿"s2"‿"s3"‿"2"
  "assign"‿"3"‿"V"‿"N"‿"N"‿"0",   "assign"‿"2"‿"pat"‿"N"‿"N"‿"1"
  "field"‿"1"‿"skip"‿"N"‿"N"‿"0"
  "dmod1"‿"2"‿"V"‿"N"‿"N"‿"0",    "dmod1"‿"1"‿"skip"‿"N"‿"N"‿"1"
  "dmod2"‿"3"‿"V"‿"N"‿"N"‿"0",    "dmod2"‿"2"‿"V"‿"N"‿"N"‿"1",    "dmod2"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "datop"‿"1"‿"V"‿"N"‿"N"‿"0",    "datop"‿"2"‿"V"‿"N"‿"N"‿"1"
  "dfork"‿"*"‿"V"‿"N"‿"N"‿"*"
  "aatop"‿"2"‿"A"‿"w"‿"x"‿"0",    "aatop"‿"1"‿"A"‿"N"‿"s2"‿"1"
  "afork"‿"3"‿"A"‿"w"‿"x"‿"0",    "afork"‿"1"‿"A"‿"w"‿"x"‿"1",    "afork"‿"2"‿"A"‿"s1"‿"s3"‿"2"
  "aswap"‿"2"‿"A"‿"x"‿"wx"‿"0",   "aswap"‿"1"‿"skip"‿"N"‿"N"‿"1"
  "aconst"‿"2"‿"V"‿"N"‿"N"‿"0",   "aconst"‿"1"‿"skip"‿"N"‿"N"‿"1"
  "abm"‿"2"‿"V"‿"N"‿"N"‿"0",      "abm"‿"1"‿"skip"‿"N"‿"N"‿"1"
  "aself1"‿"2"‿"V"‿"N"‿"N"‿"0",   "aself1"‿"1"‿"skip"‿"N"‿"N"‿"1"
  "am1d"‿"2"‿"V"‿"N"‿"N"‿"0",     "am1d"‿"1"‿"skip"‿"N"‿"N"‿"1"
  "aatop2"‿"3"‿"A"‿"w"‿"x"‿"0",   "aatop2"‿"2"‿"A"‿"N"‿"s3"‿"1",  "aatop2"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "aover1"‿"3"‿"A"‿"N"‿"x"‿"0",   "aover1"‿"2"‿"A"‿"N"‿"s3"‿"1",  "aover1"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "aover2s"‿"3"‿"callee"‿"N"‿"N"‿"0", "aover2s"‿"2"‿"A"‿"l1"‿"l0"‿"1", "aover2s"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "aover2c"‿"3"‿"V"‿"N"‿"N"‿"0",  "aover2c"‿"2"‿"A"‿"l1"‿"l0"‿"1", "aover2c"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "abefore"‿"2"‿"A"‿"N"‿"wx"‿"0", "abefore"‿"3"‿"A"‿"s2"‿"x"‿"1", "abefore"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "aafter"‿"3"‿"A"‿"N"‿"x"‿"0",   "aafter"‿"2"‿"A"‿"wx"‿"s3"‿"1", "aafter"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "aval1"‿"2"‿"A"‿"N"‿"x"‿"0",    "aval1"‿"3"‿"skip"‿"N"‿"N"‿"1", "aval1"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "aval2"‿"3"‿"A"‿"w"‿"x"‿"0",    "aval2"‿"2"‿"skip"‿"N"‿"N"‿"1", "aval2"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "aself2"‿"2"‿"V"‿"N"‿"N"‿"0",   "aself2"‿"3"‿"V"‿"N"‿"N"‿"1",   "aself2"‿"1"‿"skip"‿"N"‿"N"‿"2"
  "am2d"‿"2"‿"V"‿"N"‿"N"‿"0",     "am2d"‿"3"‿"V"‿"N"‿"N"‿"1",     "am2d"‿"1"‿"skip"‿"N"‿"N"‿"2"
⟩
rules ∾↩ ⟨"pat"‿"*"‿"pat"‿"N"‿"N"‿"*", "skip"‿"*"‿"skip"‿"N"‿"N"‿"*", "callee"‿"*"‿"skip"‿"N"‿"N"‿"*", "afield"‿"1"‿"skip"‿"N"‿"N"‿"0"⟩
ruleKey ← (⊑¨rules) {𝕨∾":"∾𝕩}¨ 1⊑¨rules


CNum ← {∾ {𝕩='¯' ? "-" ; 𝕩='∞' ? "INFINITY" ; 𝕩='π' ? "M_PI" ; ⟨𝕩⟩}¨ 𝕩}
In ← {⊑(<𝕨)∊𝕩}                       # string In list of strings
Simple ← {𝕩 In "var"‿"field"‿"spec"‿"prim"}
PrimC ← {(⊑primNames ⊐ 𝕩) ⊑ primCs}
Commas ← {0=≠𝕩 ? ⟨⟩ ; ⟨⊑𝕩⟩ ∾ ∾ {⟨", ", 𝕩⟩}¨ 1↓𝕩}       # interleave parts with ", "
Lines ← {∾ 𝕩 ∾¨ <nl}
pre ← ¯10 ⋄ mid ← 0.5 ⋄ post ← 1e6       # line positions, around a node's children

Gen ⇐ {𝕊 ty‿a1‿a2‿par‿slot:
  nn ← ≠ty
  ch ← {𝕩 ⊏˜ ⍋ 𝕩⊏slot}¨ (par ∾ nn) ⊔ ↕nn       # children of each node, by slot
  ckey ← (par + nn × slot + 1) - (par < 0) × 4×nn×nn
  Child ← {⊑ (ckey ⊐ 𝕨 + nn × 𝕩 + 1) ⊏ (↕nn) ∾ ¯1}   # node Child slot; ¯1 if none
  dep ← {(par ≥ 0) × 1 + (0⌈par) ⊏ 𝕩} _fix 0¨ty
  alive ← 0 = {𝕩⊏𝕩} _fix par + (par<0) × (↕nn) - par

  # -- top-level definitions
  stm ← 0⊑ch
  "top level: only definitions" ! ∧´ "assign" Is stm⊏ty
  lhs ← stm Child¨ 2 ⋄ rhs ← stm Child¨ 3
  "top level: define names only" ! ∧´ "var" Is lhs⊏ty
  gname ← lhs⊏a1
  GK ← {
    "sys" ≡ 𝕩⊑ty ? "k" ;
    "block" ≢ 𝕩⊑ty ? "top level: definitions must be blocks for now" ! 0 ;
    t ← 𝕩⊑a1 ⋄ d ← 𝕩⊑a2
    "immediate blocks at top level are not supported" ! t ≢ "imm"
    {t ≡ "fn" ? "fn" ; d ? t∾"d" ; t∾"i"}
  }
  gkinds ← GK¨ rhs
  gcnames ← gkinds {'d' = ¯1⊑𝕨 ? "M_"∾𝕩 ; 'i' = ¯1⊑𝕨 ? "MI_"∾𝕩 ; "F_"∾𝕩}¨ gname
  GKind ← {(⊑gname ⊐ <𝕩) ⊑ gkinds ∾ <""}
  GCname ← {(⊑gname ⊐ <𝕩) ⊑ gcnames ∾ <""}
  fns ← ("fn" Is gkinds) / gname
  exports ← (("fn" Is gkinds) ∧ '⇐' = stm⊏a1) / gname

  # -- 1. usage, one level at a time
  mode ← nn⥊<"" ⋄ aw ← nn⥊¯1 ⋄ ax ← nn⥊¯1
  fid ← nn⥊¯1 ⋄ acall ← nn⥊0 ⋄ key ← nn⥊<⟨⟩
  mode ↩ "prog"⌾(0⊸⊑) mode
  FKind ← {
    "dblock" ≡ 𝕩⊑mode ? "local" ;
    (⊑"fn"‿"m1d"‿"m2d"‿"m1i"‿"m2i" ⊐ <(⊑rhs⊐𝕩)⊑gkinds) ⊑ "fn"‿"m1"‿"m2"‿"imm1"‿"imm2"
  }
  VMode ← {
    i ← 𝕩 ⋄ t ← i⊑ty
    {
      t In "num"‿"chr"‿"str"‿"var"‿"spec"‿"field"‿"call1"‿"call2"‿"assign" ? t ;
      t ≡ "list" ? (0 = ≠i⊑ch) ⊑ "list"‿"list0" ;
      t ≡ "prim" ? "primv" ;
      t In "mod1"‿"mod2"‿"atop"‿"fork" ? (⊑"mod1"‿"mod2"‿"atop"‿"fork" ⊐ <t) ⊑ "dmod1"‿"dmod2"‿"datop"‿"dfork" ;
      t ≡ "block" ? "only function blocks can be local" ! "fn" ≡ i⊑a1 ⋄ "dblock" ;
      ("cannot compile "∾t) ! 0
    }
  }
  ModA1 ← {
    i ← 𝕩 ⋄ m ← i Child 1 ⋄ mt ← m⊑ty ⋄ mv ← m⊑a1
    {
      (mt ≡ "prim") ∧ mv ≡ '˜' ? "aswap"‿0 ;
      (mt ≡ "prim") ∧ mv ≡ '˙' ? "aconst"‿0 ;
      mt ≡ "field" ? "abm"‿0 ;
      (mt ≡ "spec") ∧ (mv ≡ "_𝕣") ∧ "m1" ≡ FKind i⊑fid ? "aself1"‿0 ;
      (mt ≡ "var") ∧ "m1d" ≡ GKind mv ? "am1d"‿0 ;
      "dmod1"‿1
    }
  }
  ModA2 ← {
    mon ← 𝕨 ⋄ i ← 𝕩 ⋄ m ← i Child 1 ⋄ mt ← m⊑ty ⋄ mv ← m⊑a1
    P ← {(mt ≡ "prim") ∧ mv ≡ 𝕩}
    {
      P '∘' ? "aatop2"‿0 ;
      P '○' ? (mon ⊑ ⟨(Simple (i Child 3)⊑ty) ⊑ "aover2c"‿"aover2s", "aover1"⟩)‿0 ;
      P '⊸' ? "abefore"‿0 ;
      P '⟜' ? "aafter"‿0 ;
      P '⊘' ? (mon ⊑ "aval2"‿"aval1")‿0 ;
      (mt ≡ "spec") ∧ (mv ≡ "_𝕣_") ∧ "m2" ≡ FKind i⊑fid ? "aself2"‿0 ;
      (mt ≡ "var") ∧ "m2d" ≡ GKind mv ? "am2d"‿0 ;
      "dmod2"‿1
    }
  }
  AMode ← {
    mon ← 𝕨 ⋄ i ← 𝕩 ⋄ t ← i⊑ty
    {
      t ≡ "var" ? "avar"‿0 ;
      t ≡ "field" ? "afield"‿0 ;
      t ≡ "spec" ? ("𝕊" ≡ i⊑a1) ⊑ ⟨"aspec"‿0, "aself"‿0⟩ ;
      t ≡ "prim" ? (⊑"⊢⊣!" ⊐ i⊑a1) ⊑ ⟨"aright"‿0, "aleft"‿0, "aassert"‿0, "primv"‿1⟩ ;
      t In "num"‿"chr"‿"str"‿"list" ? (VMode i)‿0 ;
      t ≡ "atop" ? "aatop"‿0 ;
      t ≡ "fork" ? "afork"‿0 ;
      t In "call1"‿"call2"‿"assign"‿"block" ? (VMode i)‿1 ;
      t ≡ "mod1" ? ModA1 i ;
      t ≡ "mod2" ? mon ModA2 i ;
      ("cannot compile "∾t) ! 0
    }
  }
  TopMode ← {"sys" ≡ 𝕩⊑ty ? "skip" ; 'i' = ¯1⊑(⊑rhs⊐𝕩)⊑gkinds ? "imm" ; "fn"}
  SrcOf ← {
    𝕨 ≡ "N" ? ¯1 ;
    𝕨 ≡ "w" ? 𝕩⊑aw ;
    𝕨 ≡ "x" ? 𝕩⊑ax ;
    𝕨 ≡ "wx" ? (¯1 = 𝕩⊑aw) ⊑ (𝕩⊑aw)‿(𝕩⊑ax) ;
    's' = ⊑𝕨 ? 𝕩 Child (1⊑𝕨)-'0' ;
    ¯2 - (2×𝕩) + (1⊑𝕨)-'0'
  }
  {𝕊 lev:
    ns ← /(dep = lev) ∧ alive
    p ← ns⊏par ⋄ pm ← p⊏mode ⋄ sl ← ns⊏slot
    k1 ← ruleKey ⊐ pm {𝕨∾":"∾•Fmt 𝕩}¨ sl
    k2 ← ruleKey ⊐ pm ∾¨ <":*"
    ri ← k1 + (k1 = ≠ruleKey) × k2 - k1
    ("no rule for "∾•Fmt (ri = ≠ruleKey)/pm) ! ∧´ ri < ≠ruleKey
    r ← ri ⊏ rules
    fid ↩ (p + (¬pm In¨ <"fn"‿"imm"‿"dblock") × (p⊏fid) - p)⌾(ns⊸⊏) fid
    aw ↩ ((3⊑¨r) SrcOf¨ p)⌾(ns⊸⊏) aw
    ax ↩ ((4⊑¨r) SrcOf¨ p)⌾(ns⊸⊏) ax
    rk ← (5⊑¨r) {𝕨 ≡ "*" ? 𝕩 ; •ParseFloat 𝕨}¨ sl
    key ↩ ((p⊏key) ∾¨ rk)⌾(ns⊸⊏) key
    ma ← (2⊑¨r) {
      𝕨 ≡ "V" ? (VMode 𝕩)‿0 ;
      𝕨 ≡ "A" ? (¯1 = 𝕩⊑aw) AMode 𝕩 ;
      𝕨 ≡ "top" ? (TopMode 𝕩)‿0 ;
      𝕨‿0
    }¨ ns
    mode ↩ (⊑¨ma)⌾(ns⊸⊏) mode
    acall ↩ (1⊑¨ma)⌾(ns⊸⊏) acall
  }¨ 1 + ↕⌈´ alive/dep
  isB ← ("body" Is mode) ∨ "ibody" Is mode
  bodyOf ← {(↕nn) + (¬isB) × ((0⌈par)⊏𝕩) - ↕nn} _fix nn⥊¯1

  # -- 2. lines and results
  #
  # A line is ⟨position, function, kind, parts, name⟩. Kind 0 is plain, 1
  # defines a temporary, 2 defines the variable name, 3 is an alias with no
  # text whose value is its one part. Function @ means the node's own.
  # A part is a string or a reference:
  #   ⟨"s", n⟩     result of node n: NONE for ¯1, and ¯2-2p-k is line k of p
  #   ⟨"l", p, k⟩  line k of node p (p ¯1: this node)
  #   ⟨"t"⟩ ⟨"v"⟩  this line's temporary or variable
  #   ⟨"av", n⟩    callee for name n: "call(v, " or "F_x(NULL, "
  #   ⟨"cn", f⟩    C name of function f
  #   ⟨"L", n⟩     name and environment of local function n
  # A result is ⟨"lit", s⟩, ⟨"src", n⟩, ⟨"line", k⟩, ⟨"str"⟩ or ⟨"var"⟩.
  S ← {𝕩 ≥ ¯1 ? ⟨"s", 𝕩⟩ ; ⟨"l", ⌊(¯2-𝕩)÷2, 2|¯2-𝕩⟩}
  TL ← {⟨𝕨, @, 1, ⟨"  V ", ⟨"t"⟩, " = "⟩ ∾ 𝕩 ∾ ⟨";"⟩, ""⟩}
  PL ← {⟨𝕨, @, 0, 𝕩, ""⟩}
  specs ← "𝕩"‿"𝕨"‿"𝕗"‿"𝔽"‿"𝕘"‿"𝔾"
  Specx ← {𝕩 In specs ? (⊑specs ⊐ <𝕩) ⊑ "x"‿"w"‿"e[0]"‿"e[0]"‿"e[1]"‿"e[1]" ; ("unsupported special name "∾𝕩) ! 0}
  ECall ← {𝕩 In "fn"‿"imm1"‿"imm2" ? "NULL" ; "e"}
  Callee ← {   # ⟨position, w, x⟩ Callee g: the line applying simple node g
    p‿w‿x ← 𝕨 ⋄ g ← 𝕩 ⋄ t ← g⊑ty ⋄ v ← g⊑a1
    {
      t ≡ "var" ? p TL ⟨⟨"av", g⟩, S w, ", ", S x, ")"⟩ ;
      t ≡ "field" ? p TL ⟨"b_"∾v∾"(", S w, ", ", S x, ")"⟩ ;
      (t ≡ "spec") ∧ v ≡ "𝕊" ? p TL ⟨⟨"cn", g⊑fid⟩, "("∾(ECall FKind g⊑fid)∾", ", S w, ", ", S x, ")"⟩ ;
      t ≡ "spec" ? p TL ⟨"call("∾(Specx v)∾", ", S w, ", ", S x, ")"⟩ ;
      v ≡ '⊢' ? ⟨p, @, 3, ⟨S x⟩, ""⟩ ;
      v ≡ '⊣' ? ⟨p, @, 3, ⟨S (¯1 = w) ⊑ w‿x⟩, ""⟩ ;
      v ≡ '!' ? p TL ⟨"p_assert(", S w, ", ", S x, ")"⟩ ;
      "unsupported function" ! 0
    }
  }
  BindPat ← {
    𝕊 pt‿r: "var" ≡ pt⊑ty ? ⟨⟨post, @, 2, ⟨"  V ", ⟨"v"⟩, " = ", S r, ";"⟩, pt⊑a1⟩⟩ ;
    𝕊 pt‿r: "list" ≢ pt⊑ty ? ("cannot assign to "∾pt⊑ty) ! 0 ;
    𝕊 pt‿r:
    its ← pt⊑ch
    "nested patterns are not supported" ! ∧´ "var" Is its⊏ty
    ⟨post PL ⟨"  need_list(", S r, ", "∾(•Fmt ≠its)∾");"⟩⟩ ∾ ∾ (↕≠its) {
      ⟨(post+1+2×𝕨) TL ⟨"list_get(", S r, ", "∾(•Fmt 𝕨)∾")"⟩
       ⟨post+2+2×𝕨, @, 2, ⟨"  V ", ⟨"v"⟩, " = ", ⟨"l", ¯1, 1+2×𝕨⟩, ";"⟩, 𝕩⊑a1⟩⟩
    }¨ its
  }
  DM1 ← {   # value of a 1-modifier applied to its operand
    i ← 𝕩 ⋄ mm ← i Child 1 ⋄ mt ← mm⊑ty ⋄ mv ← mm⊑a1 ⋄ f ← S i Child 2
    {
      mt ≡ "prim" ? ⟨"mk_fn("∾(PrimC mv)∾", 1, ", f, ")"⟩ ;
      mt ≡ "field" ? ⟨"mk_fn(KM_"∾mv∾", 1, ", f, ")"⟩ ;
      (mt ≡ "spec") ∧ (mv ≡ "_𝕣") ∧ "m1" ≡ FKind i⊑fid ? ⟨"mk_fn(", ⟨"cn", i⊑fid⟩, ", 1, ", f, ")"⟩ ;
      (mt ≡ "var") ∧ "m1d" ≡ GKind mv ? ⟨"mk_fn("∾(GCname mv)∾", 1, ", f, ")"⟩ ;
      (mt ≡ "var") ∧ "m1i" ≡ GKind mv ? ⟨(GCname mv)∾"(", f, ")"⟩ ;
      "unsupported 1-modifier" ! 0
    }
  }
  DM2 ← {
    i ← 𝕩 ⋄ mm ← i Child 1 ⋄ mt ← mm⊑ty ⋄ mv ← mm⊑a1 ⋄ f ← S i Child 2 ⋄ g ← S i Child 3
    {
      mt ≡ "prim" ? ⟨"mk_fn("∾(PrimC mv)∾", 2, ", f, ", ", g, ")"⟩ ;
      (mt ≡ "spec") ∧ (mv ≡ "_𝕣_") ∧ "m2" ≡ FKind i⊑fid ? ⟨"mk_fn(", ⟨"cn", i⊑fid⟩, ", 2, ", f, ", ", g, ")"⟩ ;
      (mt ≡ "var") ∧ "m2d" ≡ GKind mv ? ⟨"mk_fn("∾(GCname mv)∾", 2, ", f, ", ", g, ")"⟩ ;
      (mt ≡ "var") ∧ "m2i" ≡ GKind mv ? ⟨(GCname mv)∾"(", f, ", ", g, ")"⟩ ;
      "unsupported 2-modifier" ! 0
    }
  }
  HdrOf ← {⊑ ((¯1 = (𝕩⊑ch)⊏slot) / 𝕩⊑ch) ∾ ¯1}
  StmtsOf ← {(¯1 ≠ (𝕩⊑ch)⊏slot) / 𝕩⊑ch}
  Valences ← {   # valence of each body of a block
    n ← ≠𝕩
    hd ← HdrOf¨ 𝕩
    unc ← (hd < 0) ∧ ¬{∨´ "pred" Is (StmtsOf 𝕩) ⊏ a1}¨ 𝕩
    "headerless bodies must come last" ! ∧´ (∨`unc) ≤ unc
    "at most two headerless bodies" ! 2 ≥ +´unc
    two ← 2 = +´unc
    hd {𝕨 ≥ 0 ? ((𝕨 Child 1) ≥ 0) ⊑ ⟨((𝕨 Child 2) ≥ 0) ⊑ "any"‿"mon", "dy"⟩ ; two ∧ 𝕩⊑unc ? (𝕩 = n-2) ⊑ "dy"‿"mon" ; "any"}¨ ↕n
  }
  Body ← {
    i ← 𝕩 ⋄ j ← i⊑slot
    v ← j ⊑ Valences (i⊑par)⊑ch
    nx ← "b"∾•Fmt j+1
    st ← StmtsOf i
    "a body can't end in a predicate" ! "expr" ≡ (¯1⊑st)⊑a1
    ∾⟨
      ⟨pre PL ⟨"  b"∾(•Fmt j)∾":; {"⟩⟩
      ("mon"≡v) / ⟨(pre+1) PL ⟨"  if (w != NONE) goto "∾nx∾";"⟩⟩
      ("dy"≡v) / ⟨(pre+1) PL ⟨"  if (w == NONE) goto "∾nx∾";"⟩⟩
      ⟨post PL ⟨"  return ", S ¯1⊑st, ";"⟩, (post+1) PL ⟨"  }"⟩⟩
    ⟩
  }
  aliasSlot ← ⟨"aatop", "afork", "aswap", "aconst", "aatop2", "aover1", "aover2s", "aover2c", "abefore", "aafter", "aval1", "aval2"⟩ ⋈ 1‿2‿2‿2‿2‿2‿2‿2‿3‿2‿2‿3
  Emit ← {
    i ← 𝕩 ⋄ m ← i⊑mode ⋄ v ← i⊑a1 ⋄ k ← i⊑ch
    wv ← S i⊑aw ⋄ xv ← S i⊑ax ⋄ C ← {i Child 𝕩} ⋄ SC ← {S i Child 𝕩}
    cn ← ⟨"cn", i⊑fid⟩
    fk ← {0 ≤ i⊑fid ? FKind i⊑fid ; ""}
    Line0 ← {⟨𝕩, ⟨"line", 0⟩⟩}
    r ← {
      m ≡ "num" ? ⟨⟨⟩, ⟨"lit", "N("∾(CNum v)∾")"⟩⟩ ;
      m ≡ "chr" ? ⟨⟨⟩, ⟨"lit", "C("∾(•Fmt v-@)∾")"⟩⟩ ;
      m ≡ "str" ? ⟨⟨⟩, ⟨"str"⟩⟩ ;
      m ≡ "list0" ? ⟨⟨⟩, ⟨"lit", "mk_list(0, NULL)"⟩⟩ ;
      m ≡ "list" ? Line0 ⟨post TL ⟨"mk_list("∾(•Fmt ≠k)∾", (V[]){"⟩ ∾ (Commas S¨ k) ∾ ⟨"})"⟩⟩ ;
      m ≡ "var" ? ⟨⟨⟩, ⟨"var"⟩⟩ ;
      m ≡ "spec" ? {
        ¬v In "𝕊"‿"𝕤" ? ⟨⟨⟩, ⟨"lit", Specx v⟩⟩ ;
        fk ≡ "fn" ? ⟨⟨⟩, ⟨"lit", "g_"∾2↓(⊑rhs ⊐ i⊑fid)⊑gcnames⟩⟩ ;
        fk ≡ "m1" ? Line0 ⟨post TL ⟨"mk_fn(", cn, ", 1, e[0])"⟩⟩ ;
        fk ≡ "m2" ? Line0 ⟨post TL ⟨"mk_fn(", cn, ", 2, e[0], e[1])"⟩⟩ ;
        "𝕤 and 𝕊 as values are not supported in local blocks" ! 0
      } ;
      m ≡ "field" ? ⟨⟨⟩, ⟨"lit", "KV_"∾v⟩⟩ ;
      m ≡ "primv" ? ⟨⟨⟩, ⟨"lit", PrimC v⟩⟩ ;
      m In "call1"‿"call2" ? ⟨⟨⟩, ⟨"src", C 1⟩⟩ ;
      m ≡ "assign" ? ⟨BindPat (C 2)‿(C 3), ⟨"src", C 3⟩⟩ ;
      m ≡ "dmod1" ? Line0 ⟨post TL DM1 i⟩ ;
      m ≡ "dmod2" ? Line0 ⟨post TL DM2 i⟩ ;
      m ≡ "datop" ? Line0 ⟨post TL ⟨"mk_fn(D_atop, 2, ", SC 1, ", ", SC 2, ")"⟩⟩ ;
      m ≡ "dfork" ? Line0 ⟨post TL ⟨"mk_fn(D_fork, 3, ", SC 1, ", ", SC 2, ", ", SC 3, ")"⟩⟩ ;
      m ≡ "dblock" ? ⟨⟨⟨post, i, 0, ⟨"  b"∾(•Fmt ≠k)∾":; return vm_nomatch();"⟩, ""⟩, (post+1) TL ⟨"mk_fn(", ⟨"L", i⟩, ")"⟩⟩, ⟨"line", 1⟩⟩ ;
      m ≡ "fn" ? ⟨⟨⟨post, i, 0, ⟨"  b"∾(•Fmt ≠k)∾":; return vm_nomatch();"⟩, ""⟩⟩, ⟨"lit", ""⟩⟩ ;
      m In "avar"‿"afield"‿"aself"‿"aspec"‿"aassert" ? Line0 ⟨⟨post, i⊑aw, i⊑ax⟩ Callee i⟩ ;
      m ≡ "aright" ? ⟨⟨⟩, ⟨"src", i⊑ax⟩⟩ ;
      m ≡ "aleft" ? ⟨⟨⟩, ⟨"src", (¯1 = i⊑aw) ⊑ (i⊑aw)‿(i⊑ax)⟩⟩ ;
      m ≡ "aover2s" ? ⟨⟨⟨mid, ¯1, i⊑ax⟩ Callee C 3, ⟨mid+0.1, ¯1, i⊑aw⟩ Callee C 3⟩, ⟨"src", C 2⟩⟩ ;
      m ≡ "aover2c" ? ⟨⟨mid TL ⟨"call(", SC 3, ", NONE, ", xv, ")"⟩, (mid+0.1) TL ⟨"call(", SC 3, ", NONE, ", wv, ")"⟩⟩, ⟨"src", C 2⟩⟩ ;
      m In ⊑aliasSlot ? ⟨⟨⟩, ⟨"src", C (⊑(⊑aliasSlot) ⊐ <m) ⊑ 1⊑aliasSlot⟩⟩ ;
      m ≡ "abm" ? Line0 ⟨post TL ⟨"bm_"∾((C 1)⊑a1)∾"(", SC 2, ", ", wv, ", ", xv, ")"⟩⟩ ;
      m ≡ "aself1" ? Line0 ⟨post TL ⟨cn, "((V[]){", SC 2, "}, ", wv, ", ", xv, ")"⟩⟩ ;
      m ≡ "am1d" ? Line0 ⟨post TL ⟨(GCname (C 1)⊑a1)∾"((V[]){", SC 2, "}, ", wv, ", ", xv, ")"⟩⟩ ;
      m ≡ "aself2" ? Line0 ⟨post TL ⟨cn, "((V[]){", SC 2, ", ", SC 3, "}, ", wv, ", ", xv, ")"⟩⟩ ;
      m ≡ "am2d" ? Line0 ⟨post TL ⟨(GCname (C 1)⊑a1)∾"((V[]){", SC 2, ", ", SC 3, "}, ", wv, ", ", xv, ")"⟩⟩ ;
      m ≡ "body" ? ⟨Body i, ⟨"lit", ""⟩⟩ ;
      m ≡ "stmt" ? ⟨("pred" ≡ v) / ⟨post PL ⟨"  if (!truth(", SC 1, ")) goto b"∾(•Fmt 1+(i⊑par)⊑slot)∾";"⟩⟩, ⟨"src", C 1⟩⟩ ;
      m ≡ "istmt" ? ⟨⟨post PL ⟨"  return ", SC 1, ";"⟩⟩, ⟨"src", C 1⟩⟩ ;
      ⟨⟨⟩, ⟨"lit", ""⟩⟩
    }
    # an applied value is called: one more line, which gives the result
    {𝕤
      ls‿res ← r
      pr ← {"lit" ≡ ⊑res ? 1⊑res ; "line" ≡ ⊑res ? ⟨"l", ¯1, 1⊑res⟩ ; "src" ≡ ⊑res ? S 1⊑res ; ⟨"x", i⟩}
      r ↩ ⟨ls ∾ ⟨(post+10) TL ⟨"call(", pr, ", ", wv, ", ", xv, ")"⟩⟩, ⟨"line", ≠ls⟩⟩
    }⍟(i⊑acall) @
    r
  }

  # -- 3. order and numbering
  en ← /alive ∧ 0 < ≠¨mode
  er ← Emit¨ en
  nls ← ≠¨⊑¨er
  lnode ← nls / en
  lsN ← ((+`nls) - nls)⌾(en⊸⊏) nn⥊0          # first line of each node
  res ← (1⊑¨er)⌾(en⊸⊏) nn⥊<⟨"lit", ""⟩
  ls ← ∾ ⊑¨er ⋄ nl1 ← ≠ls
  lpos ← ⊑¨ls ⋄ lkind ← 2⊑¨ls ⋄ lname ← 4⊑¨ls
  lfn ← (1⊑¨ls) {𝕨 ≡ @ ? 𝕩⊑fid ; 𝕨}¨ lnode
  IsRef ← {2 ≤ ≡𝕩}
  lparts ← lnode {n ← 𝕨 ⋄ {(IsRef 𝕩) ∧ ⟨"l", ¯1⟩ ≡ 2↑𝕩 ? ⟨"l", n, 2⊑𝕩⟩ ; 𝕩}¨ 𝕩}¨ 3⊑¨ls
  lkey ← lnode {(𝕨⊑key) ∾ 𝕩}¨ lpos
  ord ← ⍋ lkey
  sl ← ord ⊏˜ ⍋ ord⊏lfn                      # by function, then in order
  gs ← Starts sl⊏lfn
  lt ← (gs SegSum 1 = sl⊏lkind)⌾(sl⊸⊏) nl1⥊0    # temporary number of each line
  lv ← (gs SegSum 2 = sl⊏lkind)⌾(sl⊸⊏) nl1⥊0    # variable number
  vnames ← lname {"v_"∾𝕨∾"_"∾•Fmt 𝕩}¨ lv
  # strings, basis values and modifiers, and local functions: first use order
  Byk ← {𝕩 ⊏˜ ⍋ 𝕩⊏key}
  strs ← ⍷ (Byk /alive ∧ "str" Is mode) ⊏ a1
  kvals ← ⍷ (Byk /alive ∧ "field" Is mode) ⊏ a1
  dmone ← Byk /alive ∧ "dmod1" Is mode
  dm1m ← dmone Child¨ 1
  kmods ← ⍷ (("field" Is dm1m⊏ty) / dm1m) ⊏ a1
  locs ← Byk /alive ∧ "dblock" Is mode
  funcs ← (/alive ∧ ("fn" Is mode) ∨ "imm" Is mode) ∾ locs
  FName ← {⊑𝕩∊locs ? "L_"∾•Fmt 1 + ⊑locs⊐𝕩 ; (⊑rhs⊐𝕩)⊑gcnames}

  # -- 4. names
  # binders: assignments (lines that define a variable) and header names
  bl ← /2 = lkind
  bf ← bl⊏lfn ⋄ bb ← (bl⊏lnode)⊏bodyOf ⋄ bnm ← bl⊏lname ⋄ bk ← bl⊏lkey ⋄ btx ← bl⊏vnames
  hbs ← /alive ∧ "body" Is mode
  hh ← HdrOf¨ hbs
  hbs ↩ (hh ≥ 0)/hbs ⋄ hh ↩ (hh ≥ 0)/hh
  hc ← hh Child⌜ 1+↕4
  hty ← (0⌈hc) ⊏ ty
  hv ← (hc ≥ 0) ∧ "var" Is hty
  "header patterns other than names are not supported" ! ∧´⥊ (hc < 0) ∨ hv ∨ "spec" Is hty
  hrow ← / +´˘hv
  bf ∾↩ hrow ⊏ hbs⊏fid
  bb ∾↩ hrow ⊏ hbs
  bnm ∾↩ (⥊hv) / ⥊ (0⌈hc) ⊏ a1
  bk ∾↩ hrow ⊏ (hbs⊏key) ∾¨ pre-5
  btx ∾↩ (⥊hv) / ⥊ (≢hv) ⥊ "w"‿"x"‿"e[0]"‿"e[1]"
  # uses, and the latest binder before each, by a binary search
  qn ← /alive ∧ ("var" Is mode) ∨ ("avar" Is mode) ∨ ("callee" Is mode) ∧ "var" Is ty
  names ← ⍷ bnm ∾ qn⊏a1
  Tri ← {<˘⍉>𝕩}
  bkc ← (Tri bf‿bb‿(names⊐bnm)) ∾¨ bk
  bo ← ⍋ bkc ⋄ bks ← (bo⊏bkc) ∾ <⟨∞⟩
  Find ← {𝕊 f‿b‿n‿k:   # binder of name n before key k in function f, body b
    q ← (Tri f‿b‿n) ∾¨ k
    c ← ¯1 + bks ⍋ q
    ok ← (c ≥ 0) ∧ (3↑¨(0⌈c)⊏bks) ≡¨ 3↑¨q
    ¯1 + ok × 1 + (0⌈c)⊏bo∾0
  }
  # not found in a local function: look again in the enclosing one, at the
  # block; one step per iteration
  qf ← qn⊏fid ⋄ qni ← names ⊐ qn⊏a1 ⋄ qk ← qn⊏key
  Step ← {𝕊 cf‿cb‿ck‿hp‿fd:
    act ← fd = ¯2
    r ← Find cf‿cb‿qni‿ck
    loc ← "dblock" Is cf⊏mode
    mv ← act ∧ (r < 0) ∧ loc
    nf ← r - (r < 0) ∧ loc
    ⟨cf + mv × (cf⊏fid) - cf, cb + mv × (cf⊏bodyOf) - cb, (mv/cf⊏key)⌾(mv⊸/) ck, hp + mv, fd + act × nf - fd⟩
  }
  qfin ← Step _fix ⟨qf, qn⊏bodyOf, qk, 0¨qn, ¯2¨qn⟩
  qh ← 3⊑qfin ⋄ qfd ← 4⊑qfin
  # captures: each local function a name passed through, in order of first use
  cq ← /(qfd ≥ 0) ∧ qh ≥ 1
  reqs ← ⟨⟨⟨⟩, ⟨⟩, ⟨⟩⟩⟩
  cf ← cq⊏qf
  {𝕊 j:
    m ← j < cq⊏qh
    reqs ∾↩ <⟨m/cf, m/cq⊏qni, m/cq⊏qk⟩
    cf ↩ cf⊏fid
  }¨ ↕⌈´0∾cq⊏qh
  rf‿rn‿rk ← ∾¨ <˘⍉> reqs
  ro ← ⍋ rk
  rf ↩ ro⊏rf ⋄ rn ↩ ro⊏rn
  caps ← {⍷ (rf = 𝕩) / rn}¨ locs
  CapIdx ← {⊑ ((⊑locs⊐𝕨)⊑caps) ⊐ 𝕩}            # function CapIdx name
  qtext ← {i ← 𝕩 ⋄ {(i⊑qfd) < 0 ? "" ; 0 = i⊑qh ? (i⊑qfd)⊑btx ; "e["∾(•Fmt (i⊑qf) CapIdx i⊑qni)∾"]"}}¨ ↕≠qn
  Global ← {
    ¬𝕩 In gname ? ("undefined name "∾𝕩) ! 0 ;
    "fn" ≢ GKind 𝕩 ? ("modifier "∾𝕩∾" used as a value") ! 0 ;
    @
  }
  Vtext ← {i ← ⊑qn⊐𝕩 ⋄ nm ← 𝕩⊑a1 ⋄ {0 < ≠i⊑qtext ? i⊑qtext ; Global nm ⋄ "g_"∾nm}}
  AvText ← {i ← ⊑qn⊐𝕩 ⋄ nm ← 𝕩⊑a1 ⋄ {0 < ≠i⊑qtext ? "call("∾(i⊑qtext)∾", " ; Global nm ⋄ (GCname nm)∾"(NULL, "}}
  envs ← {
    l ← 𝕩 ⋄ p ← l⊑fid ⋄ ns ← (⊑locs⊐l)⊑caps ⋄ m ← ≠ns
    r ← Find ⟨m⥊p, m⥊l⊑bodyOf, ns, m⥊<l⊑key⟩
    r {𝕨 ≥ 0 ? 𝕨⊑btx ; "e["∾(•Fmt p CapIdx 𝕩)∾"]"}¨ ns
  }¨ locs

  # -- 5. text
  Src ← {𝕩 = ¯1 ? "NONE" ; 𝕩 ≥ 0 ? ResText 𝕩 ; LineVal ((⌊(¯2-𝕩)÷2)⊑lsN) + 2|¯2-𝕩}
  LineVal ← {3 = 𝕩⊑lkind ? 𝕩 Ex ⊑𝕩⊑lparts ; "t"∾•Fmt 𝕩⊑lt}
  ResText ← {
    n ← 𝕩 ⋄ r ← n⊑res
    {
      "lit" ≡ ⊑r ? 1⊑r ;
      "line" ≡ ⊑r ? LineVal (n⊑lsN) + 1⊑r ;
      "src" ≡ ⊑r ? Src 1⊑r ;
      "str" ≡ ⊑r ? "S"∾•Fmt ⊑strs ⊐ <n⊑a1 ;
      Vtext n
    }
  }
  LText ← {e ← (⊑locs⊐𝕩)⊑envs ⋄ (FName 𝕩)∾", "∾(•Fmt ≠e)∾∾", "⊸∾¨e}
  Ex ← {
    ¬IsRef 𝕩 ? 𝕩 ;
    "t" ≡ ⊑𝕩 ? "t"∾•Fmt 𝕨⊑lt ;
    "v" ≡ ⊑𝕩 ? 𝕨⊑vnames ;
    "s" ≡ ⊑𝕩 ? Src 1⊑𝕩 ;
    "l" ≡ ⊑𝕩 ? LineVal ((1⊑𝕩)⊑lsN) + 2⊑𝕩 ;
    "av" ≡ ⊑𝕩 ? AvText 1⊑𝕩 ;
    "cn" ≡ ⊑𝕩 ? FName 1⊑𝕩 ;
    "L" ≡ ⊑𝕩 ? LText 1⊑𝕩 ;
    ("bad part "∾•Fmt 𝕩) ! 0
  }

  # -- 6. assembly, in the order c.bqn writes it
  fo ← funcs ⊏˜ ⍒ (⌽ord⊏lfn) ⊐ funcs              # functions in the order they end
  Sig ← {
    k ← FKind 𝕩 ⋄ n ← FName 𝕩
    {k In "fn"‿"m1"‿"m2"‿"local" ? "static V "∾n∾"(V *e, V w, V x)" ; k ≡ "imm1" ? "static V "∾n∾"(V f0)" ; "static V "∾n∾"(V f0, V g0)"}
  }
  PreLine ← {k ← FKind 𝕩 ⋄ {k ≡ "imm1" ? "  V e[1] = {f0};" ; k ≡ "imm2" ? "  V e[2] = {f0, g0};" ; "  (void)e; (void)w; (void)x;"}}
  FLines ← {l ← (𝕩 = ord⊏lfn) / ord ⋄ l ↩ (3 ≠ l⊏lkind) / l ⋄ {∾ 𝕩 Ex¨ 𝕩⊑lparts}¨ l}
  defs ← {Lines ⟨(Sig 𝕩)∾" {", PreLine 𝕩⟩ ∾ (FLines 𝕩) ∾ ⟨"}", ""⟩}¨ fo
  StrInit ← {"  S"∾(•Fmt 𝕨)∾" = str_lit((const uint32_t[]){"∾(∾(•Fmt¨ 𝕩-@)∾¨<", ")∾"0}, "∾(•Fmt ≠𝕩)∾");"}
  Lines ∾⟨
    ⟨"// Generated by src/c.bqn. Do not edit.", ""⟩
    {"static V g_"∾𝕩∾";"}¨ fns
    {"static V S"∾(•Fmt 𝕩)∾";"}¨ ↕≠strs
    {"static V KV_"∾𝕩∾";"}¨ kvals
    {"static V KF_"∾𝕩∾"(V *e, V w, V x) { (void)e; return b_"∾𝕩∾"(w, x); }"}¨ kvals
    {"static V KM_"∾𝕩∾"(V *e, V w, V x) { return bm_"∾𝕩∾"(e[0], w, x); }"}¨ kmods
    ({(Sig 𝕩)∾";"}¨ fo) ∾ ⟨""⟩
    defs
    ⟨"static void gen_init(void) {"⟩
    (↕≠strs) StrInit¨ strs
    {"  KV_"∾𝕩∾" = fn_static(KF_"∾𝕩∾");"}¨ kvals
    {"  g_"∾𝕩∾" = fn_static(F_"∾𝕩∾");"}¨ fns
    ⟨"}", "", "static const struct { const char *name; V *val; } gen_exports[] = {"⟩
    {"  {"""∾𝕩∾""", &g_"∾𝕩∾"},"}¨ exports
    ⟨"  {0, 0}", "};"⟩
  ⟩
}

Compile ⇐ {Gen Parse Lex d.Check 𝕩}
