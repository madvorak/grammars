import context_sensitive.csg


inductive Te
| a_ : Te
| b_ : Te
| c_ : Te

inductive Nt
| B_ : Nt
| C_ : Nt
| R_ : Nt
| S_ : Nt
| X_ : Nt
| Y_ : Nt
| Z_ : Nt

private def a : symbol Te Nt := symbol.terminal Te.a_
private def b : symbol Te Nt := symbol.terminal Te.b_
private def c : symbol Te Nt := symbol.terminal Te.c_

private def B : symbol Te Nt := symbol.nonterminal Nt.B_
private def C : symbol Te Nt := symbol.nonterminal Nt.C_
private def R : symbol Te Nt := symbol.nonterminal Nt.R_
private def S : symbol Te Nt := symbol.nonterminal Nt.S_
private def X : symbol Te Nt := symbol.nonterminal Nt.X_
private def Y : symbol Te Nt := symbol.nonterminal Nt.Y_
private def Z : symbol Te Nt := symbol.nonterminal Nt.Z_


/-- rule `S → aSBC | aRC` as two context-sensitive rules -/
private def r₁ : csrule Te Nt := csrule.mk [] Nt.S_ [] [a, S, B, C]
private def r₂ : csrule Te Nt := csrule.mk [] Nt.S_ [] [a, R, C]

/-- non-contracting rule `CB → BC` modelled by `CB → XB → XC → BC` which is context-sensitive -/
private def r₃  : csrule Te Nt := csrule.mk [] Nt.C_ [B] [X]
private def r₃' : csrule Te Nt := csrule.mk [X] Nt.B_ [] [C]
private def r₃'': csrule Te Nt := csrule.mk [] Nt.X_ [C] [B]

/-- non-contracting rule `RB → bR` modelled by `RB → YB → YR → bR` which is context-sensitive -/
private def r₄  : csrule Te Nt := csrule.mk [] Nt.R_ [B] [Y]
private def r₄' : csrule Te Nt := csrule.mk [Y] Nt.B_ [] [R]
private def r₄'': csrule Te Nt := csrule.mk [] Nt.Y_ [R] [b]

/-- non-contracting rule `RC → bc` modelled by `RC → ZC → Zc → bc` which is context-sensitive -/
private def r₅  : csrule Te Nt := csrule.mk [] Nt.R_ [C] [Z]
private def r₅' : csrule Te Nt := csrule.mk [Z] Nt.C_ [] [c]
private def r₅'': csrule Te Nt := csrule.mk [] Nt.Z_ [c] [b]

/-- context-sensitive rule `cC → cc` -/
private def r₆ : csrule Te Nt := csrule.mk [c] Nt.C_ [] [c]


private def my_grammar : CS_grammar Te :=
CS_grammar.mk Nt Nt.S_ [r₁, r₂, r₃, r₃', r₃'', r₄, r₄', r₄'', r₅, r₅', r₅'', r₆]


/-- generate `abc` by the grammar above -/
example : [Te.a_, Te.b_, Te.c_] ∈ CS_language my_grammar :=
begin
  unfold my_grammar,

  apply CS_deri_of_tran_deri,
  {
    use r₂,
    split_ile,
    use [[], []],
    split;
    refl,
  },

  apply CS_deri_of_tran_deri,
  {
    use r₅,
    split_ile,
    use [[a], []],
    split;
    refl,
  },

  apply CS_deri_of_tran_deri,
  {
    use r₅',
    split_ile,
    use [[a], []],
    split;
    refl,
  },

  apply CS_deri_of_tran,
  {
    use r₅'',
    split_ile,
    use [[a], []],
    split;
    refl,
  },
end


private meta def CS_step (rule : pexpr) (pref post : pexpr) : tactic unit := `[
  apply CS_deri_of_tran_deri,
  tactic.use [rule],
  split_ile,
  tactic.use [pref, post],
  split;
  refl
]

/-- generate `aabbcc` by the grammar above -/
example : [Te.a_, Te.a_, Te.b_, Te.b_, Te.c_, Te.c_] ∈ CS_language my_grammar :=
begin
  unfold my_grammar,
  -- S

  CS_step ``(r₁) ``([]) ``([]),
  -- aSBC

  CS_step ``(r₂) ``([a]) ``([B, C]),
  -- aaRCBClet

  CS_step ``(r₃)   ``([a, a, R]) ``([C]),
  CS_step ``(r₃')  ``([a, a, R]) ``([C]),
  CS_step ``(r₃'') ``([a, a, R]) ``([C]),
  -- aaRBCC

  CS_step ``(r₄)   ``([a, a]) ``([C, C]),
  CS_step ``(r₄')  ``([a, a]) ``([C, C]),
  CS_step ``(r₄'') ``([a, a]) ``([C, C]),
  -- aabRCC

  CS_step ``(r₅)   ``([a, a, b]) ``([C]),
  CS_step ``(r₅')  ``([a, a, b]) ``([C]),
  CS_step ``(r₅'') ``([a, a, b]) ``([C]),
  -- aabbcC

  CS_step ``(r₆) ``([a, a, b, b]) ``([]),
  -- aabbcc

  apply CS_deri_self,
end


private meta def combined_steps_r₃ (pre pos : pexpr) : tactic unit := `[
  CS_step ``(r₃)   pre pos,
  CS_step ``(r₃')  pre pos,
  CS_step ``(r₃'') pre pos
]

private meta def combined_steps_r₄ (pre pos : pexpr) : tactic unit := `[
  CS_step ``(r₄)   pre pos,
  CS_step ``(r₄')  pre pos,
  CS_step ``(r₄'') pre pos
]

/-- generate `aaabbbccc` by the grammar above -/
example : [Te.a_, Te.a_, Te.a_, Te.b_, Te.b_, Te.b_, Te.c_, Te.c_, Te.c_] ∈ CS_language my_grammar :=
begin
  -- S

  CS_step ``(r₁) ``([]) ``([]),
  -- aSBC

  CS_step ``(r₁) ``([a]) ``([B, C]),
  -- aaSBCBC

  CS_step ``(r₂) ``([a, a]) ``([B, C, B, C]),
  -- aaaRCBCBC

  combined_steps_r₃ ``([a, a, a, R]) ``([C, B, C]),
  -- aaaRBCCBC

  combined_steps_r₃ ``([a, a, a, R, B, C]) ``([C]),
  -- aaaRBCBCC

  combined_steps_r₃ ``([a, a, a, R, B]) ``([C, C]),
  -- aaaRBBCCC

  combined_steps_r₄ ``([a, a, a]) ``([B, C, C, C]),
  -- aaabRBCCC

  combined_steps_r₄ ``([a, a, a, b]) ``([C, C, C]),
  -- aaabbRCCC

  CS_step ``(r₅)   ``([a, a, a, b, b]) ``([C, C]),
  CS_step ``(r₅')  ``([a, a, a, b, b]) ``([C, C]),
  CS_step ``(r₅'') ``([a, a, a, b, b]) ``([C, C]),
  -- aaabbbcCC

  CS_step ``(r₆) ``([a, a, a, b, b, b]) ``([C]),
  -- aaabbbccC

  CS_step ``(r₆) ``([a, a, a, b, b, b, c]) ``([]),
  -- aaabbbccc

  apply CS_deri_self,
end


/-- generate ` a^4 . b^4 . c^4 ` by the grammar above -/
example : [Te.a_, Te.a_, Te.a_, Te.a_,
           Te.b_, Te.b_, Te.b_, Te.b_,
           Te.c_, Te.c_, Te.c_, Te.c_]
    ∈ CS_language my_grammar :=
begin

  -- .S.
  CS_step ``(r₁) ``([]) ``([]),
  -- .aSBC.

  -- a.S.BC
  CS_step ``(r₁) ``([a]) ``([B, C]),
  -- a.aSBC.BC

  -- aa.S.BCBC
  CS_step ``(r₁) ``([a, a]) ``([B, C, B, C]),
  -- aa.aSBC.BCBC

  -- aaa.S.BCBCBC
  CS_step ``(r₂) ``([a, a, a]) ``([B, C, B, C, B, C]),
  -- aaa.aRC.BCBCBC

  -- aaaaR.CB.CBCBC
  combined_steps_r₃ ``([a, a, a, a, R]) ``([C, B, C, B, C]),
  -- aaaaR.BC.CBCBC

  -- aaaaRBC.CB.CBC
  combined_steps_r₃ ``([a, a, a, a, R, B, C]) ``([C, B, C]),
  -- aaaaRBC.BC.CBC

  -- aaaaRB.CB.CCBC
  combined_steps_r₃ ``([a, a, a, a, R, B]) ``([C, C, B, C]),
  -- aaaaRB.BC.CCBC

  -- aaaaRBBCC.CB.C
  combined_steps_r₃ ``([a, a, a, a, R, B, B, C, C]) ``([C]),
  -- aaaaRBBCC.BC.C

  -- aaaaRBBC.CB.CC
  combined_steps_r₃ ``([a, a, a, a, R, B, B, C]) ``([C, C]),
  -- aaaaRBBC.BC.CC

  -- aaaaRBB.CB.CCC
  combined_steps_r₃ ``([a, a, a, a, R, B, B]) ``([C, C, C]),
  -- aaaaRBB.BC.CCC

  -- aaaa.RB.BBCCCC
  combined_steps_r₄ ``([a, a, a, a]) ``([B, B, C, C, C, C]),
  -- aaaa.bR.BBCCCC

  -- aaaab.RB.BCCCC
  combined_steps_r₄ ``([a, a, a, a, b]) ``([B, C, C, C, C]),
  -- aaaab.bR.BCCCC

  -- aaaabb.RB.CCCC
  combined_steps_r₄ ``([a, a, a, a, b, b]) ``([C, C, C, C]),
  -- aaaabb.bR.CCCC

  -- aaaabbb.RC.CCC
  CS_step ``(r₅)   ``([a, a, a, a, b, b, b]) ``([C, C, C]),
  -- aaaabbb.ZC.CCC
  CS_step ``(r₅')  ``([a, a, a, a, b, b, b]) ``([C, C, C]),
  -- aaaabbb.Zc.CCC
  CS_step ``(r₅'') ``([a, a, a, a, b, b, b]) ``([C, C, C]),
  -- aaaabbb.bc.CCC

  -- aaaabbbb.cC.CC
  CS_step ``(r₆) ``([a, a, a, a, b, b, b, b]) ``([C, C]),
  -- aaaabbbb.cc.CC

  -- aaaabbbbc.cC.C
  CS_step ``(r₆) ``([a, a, a, a, b, b, b, b, c]) ``([C]),
  -- aaaabbbbc.cc.C

  -- aaaabbbbcc.cC.
  CS_step ``(r₆) ``([a, a, a, a, b, b, b, b, c, c]) ``([]),
  -- aaaabbbbcc.cc.

  apply CS_deri_self,
end
