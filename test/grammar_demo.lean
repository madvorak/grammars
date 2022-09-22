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

private def S : znak := symbol.nonterminal S_
private def L : znak := symbol.nonterminal L_
private def R : znak := symbol.nonterminal R_
private def X : znak := symbol.nonterminal X_
private def B : znak := symbol.nonterminal B_
private def C : znak := symbol.nonterminal C_
private def K : znak := symbol.nonterminal K_

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

TODO fix.
This grammar generates a superset of the desired language.
L → aLX
LB → bL
These two rules cannot share the same nonterminal L.
R → BR
XR → R
These two rules cannot share the same nonterminal R.
-/

private def S_LR   : pravidlo := grule.mk  [] S_ [] [L, R]
private def L_aLX  : pravidlo := grule.mk  [] L_ [] [a, L, X]
private def R_BR   : pravidlo := grule.mk  [] R_ [] [B, R]
private def XB_BCX : pravidlo := grule.mk [X] B_ [] [B, C, X]
private def XC_CX  : pravidlo := grule.mk [X] C_ [] [C, X]
private def CB_BC  : pravidlo := grule.mk [C] B_ [] [B, C]
private def XR_R   : pravidlo := grule.mk [X] R_ [] [R]      -- shortens the word
private def LB_bL  : pravidlo := grule.mk [L] B_ [] [b, L]
private def L_K    : pravidlo := grule.mk  [] L_ [] [K]
private def KC_cK  : pravidlo := grule.mk [K] C_ [] [c, K]
private def KR_nil : pravidlo := grule.mk [K] R_ [] []       -- shortens the word

private def gr_mul : grammar abeceda :=
grammar.mk vnitrni S_ [S_LR, L_aLX, R_BR, XB_BCX, XC_CX, CB_BC, XR_R, LB_bL, L_K, KC_cK, KR_nil]


meta def find_in_explicit_list : tactic unit := `[
  tactic.repeat `[
    tactic.try `[apply list.mem_cons_self],
    tactic.try `[apply list.mem_cons_of_mem]
  ]
]

private meta def grammar_step (rule : pexpr) (pref post : pexpr) : tactic unit := `[
  apply grammar_deri_of_tran_deri,
  tactic.use [rule],
  split,
  {
    find_in_explicit_list,
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
  grammar_step ``(KR_nil) ``([]) ``([]),
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
  grammar_step ``(KR_nil) ``([a, b, c]) ``([]),
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
  grammar_step ``(KR_nil) ``([a, a, b, c, c]) ``([]),
  apply grammar_deri_self,
end

-- example 2 * 3 = 6
example : grammar_generates gr_mul [a_, a_, b_, b_, b_, c_, c_, c_, c_, c_, c_] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  grammar_step ``(L_aLX) ``([]) ``([R]),
  grammar_step ``(L_aLX) ``([a]) ``([X, R]),
  grammar_step ``(R_BR) ``([a, a, L, X, X]) ``([]),
  grammar_step ``(R_BR) ``([a, a, L, X, X, B]) ``([]),
  grammar_step ``(R_BR) ``([a, a, L, X, X, B, B]) ``([]), -- aaLXXBBBR
  grammar_step ``(XB_BCX) ``([a, a, L, X]) ``([B, B, R]),
  grammar_step ``(XB_BCX) ``([a, a, L, X, B, C]) ``([B, R]),
  grammar_step ``(XB_BCX) ``([a, a, L, X, B, C, B, C]) ``([R]),
  grammar_step ``(CB_BC) ``([a, a, L, X, B]) ``([C, B, C, X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, X, B, B, C]) ``([C, X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, X, B, B]) ``([C, C, X, R]), -- aaLXBBBCCCXR
  grammar_step ``(XB_BCX) ``([a, a, L]) ``([B, B, C, C, C, X, R]),
  grammar_step ``(XB_BCX) ``([a, a, L, B, C]) ``([B, C, C, C, X, R]),
  grammar_step ``(XB_BCX) ``([a, a, L, B, C, B, C]) ``([C, C, C, X, R]),
  grammar_step ``(XC_CX) ``([a, a, L, B, C, B, C, B, C]) ``([C, C, X, R]),
  grammar_step ``(XC_CX) ``([a, a, L, B, C, B, C, B, C, C]) ``([C, X, R]),
  grammar_step ``(XC_CX) ``([a, a, L, B, C, B, C, B, C, C, C]) ``([X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, B]) ``([C, B, C, C, C, C, X, X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, B, B, C]) ``([C, C, C, C, X, X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, B, B]) ``([C, C, C, C, C, X, X, R]), -- aaLBBB.C^6.XXR
  grammar_step ``(LB_bL) ``([a, a]) ``([B, B, C, C, C, C, C, C, X, X, R]),
  grammar_step ``(LB_bL) ``([a, a, b]) ``([B, C, C, C, C, C, C, X, X, R]),
  grammar_step ``(LB_bL) ``([a, a, b, b]) ``([C, C, C, C, C, C, X, X, R]),
  grammar_step ``(L_K) ``([a, a, b, b, b]) ``([C, C, C, C, C, C, X, X, R]), --aabbbK.C^6.XXR
  grammar_step ``(KC_cK) ``([a, a, b, b, b]) ``([C, C, C, C, C, X, X, R]),
  grammar_step ``(KC_cK) ``([a, a, b, b, b, c]) ``([C, C, C, C, X, X, R]),
  grammar_step ``(KC_cK) ``([a, a, b, b, b, c, c]) ``([C, C, C, X, X, R]),
  grammar_step ``(KC_cK) ``([a, a, b, b, b, c, c, c]) ``([C, C, X, X, R]),
  grammar_step ``(KC_cK) ``([a, a, b, b, b, c, c, c, c]) ``([C, X, X, R]),
  grammar_step ``(KC_cK) ``([a, a, b, b, b, c, c, c, c, c]) ``([X, X, R]),
  grammar_step ``(XR_R) ``([a, a, b, b, b, c, c, c, c, c, c, K, X]) ``([]),
  grammar_step ``(XR_R) ``([a, a, b, b, b, c, c, c, c, c, c, K]) ``([]),
  grammar_step ``(KR_nil) ``([a, a, b, b, b, c, c, c, c, c, c]) ``([]),
  apply grammar_deri_self,
end

-- example 3 * 3 = 9
example : grammar_generates gr_mul [a_, a_, a_, b_, b_, b_, c_, c_, c_, c_, c_, c_, c_, c_, c_] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  grammar_step ``(L_aLX) ``([]) ``([R]),
  grammar_step ``(L_aLX) ``([a]) ``([X, R]),
  grammar_step ``(R_BR) ``([a, a, L, X, X]) ``([]),
  grammar_step ``(R_BR) ``([a, a, L, X, X, B]) ``([]),
  grammar_step ``(R_BR) ``([a, a, L, X, X, B, B]) ``([]),
  grammar_step ``(XB_BCX) ``([a, a, L, X]) ``([B, B, R]),
  grammar_step ``(XB_BCX) ``([a, a, L, X, B, C]) ``([B, R]),
  grammar_step ``(XB_BCX) ``([a, a, L, X, B, C, B, C]) ``([R]),
  grammar_step ``(CB_BC) ``([a, a, L, X, B]) ``([C, B, C, X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, X, B, B, C]) ``([C, X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, X, B, B]) ``([C, C, X, R]),
  grammar_step ``(XB_BCX) ``([a, a, L]) ``([B, B, C, C, C, X, R]),
  grammar_step ``(XB_BCX) ``([a, a, L, B, C]) ``([B, C, C, C, X, R]),
  grammar_step ``(XB_BCX) ``([a, a, L, B, C, B, C]) ``([C, C, C, X, R]),
  grammar_step ``(XC_CX) ``([a, a, L, B, C, B, C, B, C]) ``([C, C, X, R]),
  grammar_step ``(XC_CX) ``([a, a, L, B, C, B, C, B, C, C]) ``([C, X, R]),
  grammar_step ``(XC_CX) ``([a, a, L, B, C, B, C, B, C, C, C]) ``([X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, B]) ``([C, B, C, C, C, C, X, X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, B, B, C]) ``([C, C, C, C, X, X, R]),
  grammar_step ``(CB_BC) ``([a, a, L, B, B]) ``([C, C, C, C, C, X, X, R]), -- aaLBBB.C^6.XXR
  grammar_step ``(L_aLX) ``([a, a]) ``([B, B, B, C, C, C, C, C, C, X, X, R]),
  grammar_step ``(XB_BCX) ``([a, a, a, L]) ``([B, B, C, C, C, C, C, C, X, X, R]),
  grammar_step ``(XB_BCX) ``([a, a, a, L, B, C]) ``([B, C, C, C, C, C, C, X, X, R]),
  grammar_step ``(XB_BCX) ``([a, a, a, L, B, C, B, C]) ``([C, C, C, C, C, C, X, X, R]),
  grammar_step ``(XC_CX) ``([a, a, a, L, B, C, B, C, B, C]) ``([C, C, C, C, C, X, X, R]),
  grammar_step ``(XC_CX) ``([a, a, a, L, B, C, B, C, B, C, C]) ``([C, C, C, C, X, X, R]),
  grammar_step ``(XC_CX) ``([a, a, a, L, B, C, B, C, B, C, C, C]) ``([C, C, C, X, X, R]),
  grammar_step ``(XC_CX) ``([a, a, a, L, B, C, B, C, B, C, C, C, C]) ``([C, C, X, X, R]),
  grammar_step ``(XC_CX) ``([a, a, a, L, B, C, B, C, B, C, C, C, C, C]) ``([C, X, X, R]),
  grammar_step ``(XC_CX) ``([a, a, a, L, B, C, B, C, B, C, C, C, C, C, C]) ``([X, X, R]),
  grammar_step ``(CB_BC) ``([a, a, a, L, B]) ``([C, B, C, C, C, C, C, C, C, X, X, X, R]),
  grammar_step ``(CB_BC) ``([a, a, a, L, B, B, C]) ``([C, C, C, C, C, C, C, X, X, X, R]),
  grammar_step ``(CB_BC) ``([a, a, a, L, B, B]) ``([C, C, C, C, C, C, C, C, X, X, X, R]),
  -- a^3.L.B^3.C^9.X^3.R
  apply grammar_deri_of_deri_deri,
  {
    change
      grammar_derives gr_mul
        ([a, a, a, L, B, B, B, C, C, C, C, C, C, C, C, C] ++ [X, X, X, R])
        ([a, a, a, L, B, B, B, C, C, C, C, C, C, C, C, C] ++ [R]),
    apply grammar_derives_with_prefix,
    grammar_step ``(XR_R) ``([X, X]) ``([]),
    grammar_step ``(XR_R) ``([X]) ``([]),
    grammar_step ``(XR_R) ``([]) ``([]),
    apply grammar_deri_self,
  },
  change
    grammar_derives gr_mul
      ([a, a, a] ++ [L, B, B, B, C, C, C, C, C, C, C, C, C, R])
      ([a, a, a] ++ [b, b, b, c, c, c, c, c, c, c, c, c]),
  apply grammar_derives_with_prefix,
  grammar_step ``(LB_bL) ``([]) ``([B, B, C, C, C, C, C, C, C, C, C, R]),
  grammar_step ``(LB_bL) ``([b]) ``([B, C, C, C, C, C, C, C, C, C, R]),
  grammar_step ``(LB_bL) ``([b, b]) ``([C, C, C, C, C, C, C, C, C, R]),
  change
    grammar_derives gr_mul
      ([b, b, b] ++ [L, C, C, C, C, C, C, C, C, C, R])
      ([b, b, b] ++ [c, c, c, c, c, c, c, c, c]),
  apply grammar_derives_with_prefix,
  grammar_step ``(L_K) ``([]) ``([C, C, C, C, C, C, C, C, C, R]),
  grammar_step ``(KC_cK) ``([]) ``([C, C, C, C, C, C, C, C, R]),
  grammar_step ``(KC_cK) ``([c]) ``([C, C, C, C, C, C, C, R]),
  grammar_step ``(KC_cK) ``([c, c]) ``([C, C, C, C, C, C, R]),
  grammar_step ``(KC_cK) ``([c, c, c]) ``([C, C, C, C, C, R]),
  grammar_step ``(KC_cK) ``([c, c, c, c]) ``([C, C, C, C, R]),
  grammar_step ``(KC_cK) ``([c, c, c, c, c]) ``([C, C, C, R]),
  grammar_step ``(KC_cK) ``([c, c, c, c, c, c]) ``([C, C, R]),
  grammar_step ``(KC_cK) ``([c, c, c, c, c, c, c]) ``([C, R]),
  grammar_step ``(KC_cK) ``([c, c, c, c, c, c, c, c]) ``([R]),
  grammar_step ``(KR_nil) ``([c, c, c, c, c, c, c, c, c]) ``([]),
  apply grammar_deri_self,
end


lemma list_repeat_succ_eq_singleton_append {α : Type*} (s : α) (n : ℕ) :
  list.repeat s n.succ = [s] ++ list.repeat s n :=
begin
  -- almost the name as `list.repeat_succ` which is a `rfl` lemma
  refl,
end

lemma list_repeat_succ_eq_append_singleton {α : Type*} (s : α) (n : ℕ) :
  list.repeat s n.succ = list.repeat s n ++ [s] :=
begin
  change list.repeat s (n + 1) = list.repeat s n ++ [s],
  rw list.repeat_add,
  refl,
end


private lemma steps_L_aLX (m : ℕ) :
  grammar_derives gr_mul [L, R] (list.repeat a m ++ [L] ++ list.repeat X m ++ [R]) :=
begin
  induction m with k ih,
  {
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran ih,
  use L_aLX,
  split,
  {
    find_in_explicit_list,
  },
  use [list.repeat a k , list.repeat X k ++ [R]],
  split,
  {
    simp [L, L_aLX, list.append_nil, list.append_assoc],
  },
  {
    rw list_repeat_succ_eq_append_singleton a,
    rw list_repeat_succ_eq_singleton_append X,
    simp [L, L_aLX, list.append_assoc],
  },
end

private lemma steps_R_BR (m n : ℕ) :
  grammar_derives gr_mul
    (list.repeat a m ++ [L] ++ list.repeat X m ++ [R])
    (list.repeat a m ++ [L] ++ list.repeat X m ++ list.repeat B n ++ [R]) :=
begin
  induction n with k ih,
  {
    rw [list.repeat, list.append_nil],
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran ih,
  use R_BR,
  split,
  {
    find_in_explicit_list,
  },
  use [list.repeat a m ++ [L] ++ list.repeat X m ++ list.repeat B k, []],
  split,
  {
    simp [R, R_BR, list.append_nil],
  },
  {
    rw list_repeat_succ_eq_append_singleton B,
    simp [R, R_BR, list.append_nil, list.append_assoc],
  },
end

private lemma steps_quadratic (m n : ℕ) :
  grammar_derives gr_mul
    (list.repeat a m ++ [L] ++ list.repeat X m ++ list.repeat B n ++ [R])
    (list.repeat a m ++ [L] ++ list.repeat B n ++ list.repeat C (m * n) ++
      list.repeat X m ++ [R]) :=
begin
  sorry
end

private lemma steps_XR_R (m n : ℕ) :
  grammar_derives gr_mul
    (list.repeat a m ++ [L] ++ list.repeat B n ++ list.repeat C (m * n) ++ list.repeat X m ++ [R])
    (list.repeat a m ++ [L] ++ list.repeat B n ++ list.repeat C (m * n) ++ [R]) :=
begin
  sorry
end

/-
private lemma steps_LB_bL (m n n' : ℕ) (le_n : n' ≤ n) :
  grammar_derives gr_mul
    (list.repeat a m ++ [L] ++ list.repeat B n ++ list.repeat C (m * n) ++ [R])
    (list.repeat a m ++ list.repeat b n' ++ [L] ++ list.repeat B (n - n') ++
      list.repeat C (m * n) ++ [R]) :=
begin
  sorry
end-/

private lemma steps_LB_bL (m n : ℕ) :
  grammar_derives gr_mul
    (list.repeat a m ++ [L] ++ list.repeat B n ++ list.repeat C (m * n) ++ [R])
    (list.repeat a m ++ list.repeat b n ++ [L] ++ list.repeat C (m * n) ++ [R]) :=
begin
  sorry
end

private lemma steps_KC_cK (m n : ℕ) :
  grammar_derives gr_mul
    (list.repeat a m ++ list.repeat b n ++ [K] ++ list.repeat C (m * n) ++ [R])
    (list.repeat a m ++ list.repeat b n ++ list.repeat c (m * n) ++ [K] ++ [R]) :=
begin
  sorry
end


-- example 2 * 3 = 6 reproved using new lemmata
example : grammar_generates gr_mul [a_, a_, b_, b_, b_, c_, c_, c_, c_, c_, c_] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  apply grammar_deri_of_deri_deri (steps_L_aLX 2),
  apply grammar_deri_of_deri_deri (steps_R_BR 2 3),
  apply grammar_deri_of_deri_deri (steps_quadratic 2 3),
  apply grammar_deri_of_deri_deri (steps_XR_R 2 3),
  apply grammar_deri_of_deri_deri (steps_LB_bL 2 3),
  grammar_step ``(L_K) ``([a, a, b, b, b]) ``([C, C, C, C, C, C, R]),
  apply grammar_deri_of_deri_deri (steps_KC_cK 2 3),
  apply grammar_deri_of_tran,
  use KR_nil,
  split,
  {
    find_in_explicit_list,
  },
  use [[a, a, b, b, b, c, c, c, c, c, c], []],
  split;
  refl,
end

-- example 19 * 21 = 399
example : grammar_generates gr_mul (list.repeat a_ 19 ++ list.repeat b_ 21 ++ list.repeat c_ 399) :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  apply grammar_deri_of_deri_deri (steps_L_aLX 19),
  apply grammar_deri_of_deri_deri (steps_R_BR 19 21),
  apply grammar_deri_of_deri_deri (steps_quadratic 19 21),
  apply grammar_deri_of_deri_deri (steps_XR_R 19 21),
  apply grammar_deri_of_deri_deri (steps_LB_bL 19 21),
  grammar_step ``(L_K) ``((list.repeat a 19 ++ list.repeat b 21)) ``(list.repeat C 399 ++ [R]),
  apply grammar_deri_of_deri_deri (steps_KC_cK 19 21),
  apply grammar_deri_of_tran,
  use KR_nil,
  split,
  {
    find_in_explicit_list,
  },
  use [(list.repeat a 19 ++ list.repeat b 21 ++ list.repeat c 399), []],
  split;
  refl,
end


private theorem multiplication_complete (m n : ℕ) :
  grammar_generates gr_mul (list.repeat a_ m ++ list.repeat b_ n ++ list.repeat c_ (m * n)) :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  apply grammar_deri_of_deri_deri (steps_L_aLX m),
  apply grammar_deri_of_deri_deri (steps_R_BR m n),
  apply grammar_deri_of_deri_deri (steps_quadratic m n),
  apply grammar_deri_of_deri_deri (steps_XR_R m n),
  apply grammar_deri_of_deri_deri (steps_LB_bL m n),
  apply grammar_deri_of_tran_deri,
  {
    use L_K,
    split,
    {
      find_in_explicit_list,
    },
    use [list.repeat a m ++ list.repeat b n, list.repeat C (m * n) ++ [R]],
    split;
    finish,
  },
  repeat {
    rw ←list.append_assoc,
  },
  apply grammar_deri_of_deri_deri (steps_KC_cK m n),
  apply grammar_deri_of_tran,
  use KR_nil,
  split,
  {
    find_in_explicit_list,
  },
  unfold KR_nil,
  use [(list.repeat a m ++ list.repeat b n ++ list.repeat c (m * n)), []],
  split,
  {
    finish,
  },
  rw list.map_append_append,
  repeat {
    rw list.map_repeat,
  },
  repeat {
    rw list.append_assoc,
  },
  congr,
  rw list.append_nil,
  rw list.append_nil,
  refl,
end
