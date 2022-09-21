import unrestricted.grammar


inductive abeceda
| _a : abeceda
| _b : abeceda
| _c : abeceda

inductive vnitrni
| _S : vnitrni
| _L : vnitrni
| _R : vnitrni
| _X : vnitrni
| _B : vnitrni
| _C : vnitrni
| _K : vnitrni

private def a_ := abeceda._a
private def b_ := abeceda._b
private def c_ := abeceda._c

private def S_ := vnitrni._S
private def L_ := vnitrni._L
private def R_ := vnitrni._R
private def X_ := vnitrni._X
private def B_ := vnitrni._B
private def C_ := vnitrni._C
private def K_ := vnitrni._K

private def znak : Type := symbol abeceda vnitrni
private def pravidlo : Type := grule abeceda vnitrni

private def a : znak := symbol.terminal a_
private def b : znak := symbol.terminal b_
private def c : znak := symbol.terminal c_

private def S : znak := symbol.nonterminal vnitrni._S
private def L : znak := symbol.nonterminal vnitrni._L
private def R : znak := symbol.nonterminal vnitrni._R
private def X : znak := symbol.nonterminal vnitrni._X
private def B : znak := symbol.nonterminal vnitrni._B
private def C : znak := symbol.nonterminal vnitrni._C
private def K : znak := symbol.nonterminal vnitrni._K

/-
Grammar for unary multiplication
{ a^m . b^n . c^(m*n) | m n ∈ ℕ }
example   2 * 3 = 6

          S
S → LR
          LR
L → aLX
          aaLXXR
R → BR
          aaLXXBBBR
XB → BCX
XC → CX
CB → BC
          aaLBBBCCCCCCXXR
XR → R
          aaLBBBCCCCCCR
LB → bL
          aabbbLCCCCCCR
L → K
          aabbbKCCCCCCR
KC → cK
          aabbbccccccKR
KR → ∅
          aabbbcccccc

0 * 0 = 0 goes S → LR → KR → ∅
3 * 0 = 0 goes S → LR → aLXR → aaLXXR → aaaLXXXR → aaaLXXR → aaaLXR → aaaLR → aaaKR → aaa
0 * 2 = 0 goes S → LR → LBR → LBBR → bLBR → bbLR → bbKR → bb
1 * 1 = 1 goes S → LR → aLXR → aLXBR → aLBCXR → aLBCR → abLCR → abKCR → abcKR → abc
-/

private def S_LR   : pravidlo := grule.mk  [] S_ [] [L, R]
private def L_aLX  : pravidlo := grule.mk  [] L_ [] [a, L, X]
private def R_BR   : pravidlo := grule.mk  [] R_ [] [B, R]
private def XB_BCX : pravidlo := grule.mk [X] B_ [] [B, C, X]
private def XC_CX  : pravidlo := grule.mk [X] C_ [] [C, X]
private def CB_BC  : pravidlo := grule.mk [C] B_ [] [B, C]
private def XR_R   : pravidlo := grule.mk [X] R_ [] [R]
private def LB_bL  : pravidlo := grule.mk [L] B_ [] [b, L]
private def L_K    : pravidlo := grule.mk  [] L_ [] [K]
private def KC_cK  : pravidlo := grule.mk [K] C_ [] [c, K]
private def KR_end : pravidlo := grule.mk [K] R_ [] []

private def gr_mul : grammar abeceda :=
grammar.mk vnitrni S_ [S_LR, L_aLX, R_BR, XB_BCX, XC_CX, CB_BC, XR_R, LB_bL, L_K, KC_cK, KR_end]


private meta def in_list_try : tactic unit := `[
  tactic.try `[apply list.mem_cons_self],
  tactic.try `[apply list.mem_cons_of_mem]
]

private meta def grammar_step (rule : pexpr) (pref post : pexpr) : tactic unit := `[
  apply grammar_deri_of_tran_deri,
  tactic.use [rule],
  split,
  {
    tactic.repeat in_list_try,
  },
  tactic.use [pref, post],
  split;
  refl
]

-- example 0 * 0 = 0
example : grammar_generates gr_mul [] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  grammar_step ``(L_K) ``([]) ``([R]),
  grammar_step ``(KR_end) ``([]) ``([]),
  apply grammar_deri_self,
end

-- example 1 * 1 = 1
example : grammar_generates gr_mul [a_, b_, c_] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  grammar_step ``(L_aLX) ``([]) ``([R]),
  grammar_step ``(R_BR) ``([a, L, X]) ``([]),
  grammar_step ``(XB_BCX) ``([a, L]) ``([R]),
  grammar_step ``(XR_R) ``([a, L, B, C]) ``([]),
  grammar_step ``(LB_bL) ``([a]) ``([C, R]),
  grammar_step ``(L_K) ``([a, b]) ``([C, R]),
  grammar_step ``(KC_cK) ``([a, b]) ``([R]),
  grammar_step ``(KR_end) ``([a, b, c]) ``([]),
  apply grammar_deri_self,
end

-- example 2 * 1 = 2
example : grammar_generates gr_mul [a_, a_, b_, c_, c_] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  grammar_step ``(L_aLX) ``([]) ``([R]),
  grammar_step ``(R_BR) ``([a, L, X]) ``([]),
  grammar_step ``(L_aLX) ``([a]) ``([X, B, R]),
  grammar_step ``(XB_BCX) ``([a, a, L, X]) ``([R]),
  grammar_step ``(XR_R) ``([a, a, L, X, B, C]) ``([]),
  grammar_step ``(XB_BCX) ``([a, a, L]) ``([C, R]),
  grammar_step ``(XC_CX) ``([a, a, L, B, C]) ``([R]),
  grammar_step ``(XR_R) ``([a, a, L, B, C, C]) ``([]),
  grammar_step ``(LB_bL) ``([a, a]) ``([C, C, R]),
  grammar_step ``(L_K) ``([a, a, b]) ``([C, C, R]),
  grammar_step ``(KC_cK) ``([a, a, b]) ``([C, R]),
  grammar_step ``(KC_cK) ``([a, a, b, c]) ``([R]),
  grammar_step ``(KR_end) ``([a, a, b, c, c]) ``([]),
  apply grammar_deri_self,
end
