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
| _M : vnitrni
| _E : vnitrni
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
private def M_ := vnitrni._M
private def E_ := vnitrni._E
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
private def M : znak := symbol.nonterminal M_
private def E : znak := symbol.nonterminal E_
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
L → M
          aaMXXBBBR
R → E
          aaMXXBBBE
XB → BCX
XC → CX
CB → BC
          aaMBBBCCCCCCXXE
XE → E
          aaMBBBCCCCCCE
MB → bM
          aabbbMCCCCCCE
M → K
          aabbbKCCCCCCE
KC → cK
          aabbbccccccKE
KE → ∅
          aabbbcccccc
-/

private def S_LR   : pravidlo := grule.mk  [] S_ [] [L, R]
private def L_aLX  : pravidlo := grule.mk  [] L_ [] [a, L, X]
private def R_BR   : pravidlo := grule.mk  [] R_ [] [B, R]
private def L_M    : pravidlo := grule.mk  [] L_ [] [M]
private def R_E    : pravidlo := grule.mk  [] R_ [] [E]
private def XB_BCX : pravidlo := grule.mk [X] B_ [] [B, C, X]
private def XC_CX  : pravidlo := grule.mk [X] C_ [] [C, X]
private def CB_BC  : pravidlo := grule.mk [C] B_ [] [B, C]
private def XE_E   : pravidlo := grule.mk [X] E_ [] [E]      -- shortens the word
private def MB_bM  : pravidlo := grule.mk [M] B_ [] [b, M]
private def M_K    : pravidlo := grule.mk  [] M_ [] [K]
private def KC_cK  : pravidlo := grule.mk [K] C_ [] [c, K]
private def KE_nil : pravidlo := grule.mk [K] E_ [] []       -- shortens the word

private def gr_mul : grammar abeceda :=
grammar.mk vnitrni S_ [S_LR, L_aLX, R_BR, L_M, R_E, XB_BCX, XC_CX, CB_BC, XE_E, MB_bM, M_K, KC_cK, KE_nil]


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
  grammar_step ``(L_M) ``([]) ``([R]),
  grammar_step ``(R_E) ``([M]) ``([]),
  grammar_step ``(M_K) ``([]) ``([E]),
  grammar_step ``(KE_nil) ``([]) ``([]),
  apply grammar_deri_self,
end

-- example 1 * 1 = 1
example : grammar_generates gr_mul [a_, b_, c_] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  grammar_step ``(L_aLX) ``([]) ``([R]),
  grammar_step ``(R_BR) ``([a, L, X]) ``([]),
  grammar_step ``(L_M) ``([a]) ``([X, B, R]),
  grammar_step ``(R_E) ``([a, M, X, B]) ``([]),
  grammar_step ``(XB_BCX) ``([a, M]) ``([E]),
  grammar_step ``(XE_E) ``([a, M, B, C]) ``([]),
  grammar_step ``(MB_bM) ``([a]) ``([C, E]),
  grammar_step ``(M_K) ``([a, b]) ``([C, E]),
  grammar_step ``(KC_cK) ``([a, b]) ``([E]),
  grammar_step ``(KE_nil) ``([a, b, c]) ``([]),
  apply grammar_deri_self,
end

-- example 2 * 1 = 2
example : grammar_generates gr_mul [a_, a_, b_, c_, c_] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  grammar_step ``(L_aLX) ``([]) ``([R]),
  grammar_step ``(R_BR) ``([a, L, X]) ``([]),
  grammar_step ``(L_aLX) ``([a]) ``([X, B, R]),
  grammar_step ``(L_M) ``([a, a]) ``([X, X, B, R]),
  grammar_step ``(R_E) ``([a, a, M, X, X, B]) ``([]),
  grammar_step ``(XB_BCX) ``([a, a, M, X]) ``([E]),
  grammar_step ``(XE_E) ``([a, a, M, X, B, C]) ``([]),
  grammar_step ``(XB_BCX) ``([a, a, M]) ``([C, E]),
  grammar_step ``(XC_CX) ``([a, a, M, B, C]) ``([E]),
  grammar_step ``(XE_E) ``([a, a, M, B, C, C]) ``([]),
  grammar_step ``(MB_bM) ``([a, a]) ``([C, C, E]),
  grammar_step ``(M_K) ``([a, a, b]) ``([C, C, E]),
  grammar_step ``(KC_cK) ``([a, a, b]) ``([C, E]),
  grammar_step ``(KC_cK) ``([a, a, b, c]) ``([E]),
  grammar_step ``(KE_nil) ``([a, a, b, c, c]) ``([]),
  apply grammar_deri_self,
end

-- example 3 * 3 = 9
example : grammar_generates gr_mul [a_, a_, a_, b_, b_, b_, c_, c_, c_, c_, c_, c_, c_, c_, c_] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  grammar_step ``(L_aLX) ``([]) ``([R]),
  grammar_step ``(L_aLX) ``([a]) ``([X, R]),
  grammar_step ``(L_aLX) ``([a, a]) ``([X, X, R]),
  grammar_step ``(R_BR) ``([a, a, a, L, X, X, X]) ``([]),
  grammar_step ``(R_BR) ``([a, a, a, L, X, X, X, B]) ``([]),
  grammar_step ``(R_BR) ``([a, a, a, L, X, X, X, B, B]) ``([]),
  grammar_step ``(L_M) ``([a, a, a]) ``([X, X, X, B, B, B, R]),
  grammar_step ``(R_E) ``([a, a, a, M, X, X, X, B, B, B]) ``([]),
  grammar_step ``(XB_BCX) ``([a, a, a, M, X, X]) ``([B, B, E]),
  grammar_step ``(XB_BCX) ``([a, a, a, M, X, X, B, C]) ``([B, E]),
  grammar_step ``(XB_BCX) ``([a, a, a, M, X, X, B, C, B, C]) ``([E]),
  grammar_step ``(CB_BC) ``([a, a, a, M, X, X, B]) ``([C, B, C, X, E]),
  grammar_step ``(CB_BC) ``([a, a, a, M, X, X, B, B, C]) ``([C, X, E]),
  grammar_step ``(CB_BC) ``([a, a, a, M, X, X, B, B]) ``([C, C, X, E]),
  grammar_step ``(XB_BCX) ``([a, a, a, M, X]) ``([B, B, C, C, C, X, E]),
  grammar_step ``(XB_BCX) ``([a, a, a, M, X, B, C]) ``([B, C, C, C, X, E]),
  grammar_step ``(XB_BCX) ``([a, a, a, M, X, B, C, B, C]) ``([C, C, C, X, E]),
  grammar_step ``(XC_CX) ``([a, a, a, M, X, B, C, B, C, B, C]) ``([C, C, X, E]),
  grammar_step ``(XC_CX) ``([a, a, a, M, X, B, C, B, C, B, C, C]) ``([C, X, E]),
  grammar_step ``(XC_CX) ``([a, a, a, M, X, B, C, B, C, B, C, C, C]) ``([X, E]),
  grammar_step ``(CB_BC) ``([a, a, a, M, X, B]) ``([C, B, C, C, C, C, X, X, E]),
  grammar_step ``(CB_BC) ``([a, a, a, M, X, B, B, C]) ``([C, C, C, C, X, X, E]),
  grammar_step ``(CB_BC) ``([a, a, a, M, X, B, B]) ``([C, C, C, C, C, X, X, E]),
  grammar_step ``(XB_BCX) ``([a, a, a, M]) ``([B, B, C, C, C, C, C, C, X, X, E]),
  grammar_step ``(XB_BCX) ``([a, a, a, M, B, C]) ``([B, C, C, C, C, C, C, X, X, E]),
  grammar_step ``(XB_BCX) ``([a, a, a, M, B, C, B, C]) ``([C, C, C, C, C, C, X, X, E]),
  grammar_step ``(XC_CX) ``([a, a, a, M, B, C, B, C, B, C]) ``([C, C, C, C, C, X, X, E]),
  grammar_step ``(XC_CX) ``([a, a, a, M, B, C, B, C, B, C, C]) ``([C, C, C, C, X, X, E]),
  grammar_step ``(XC_CX) ``([a, a, a, M, B, C, B, C, B, C, C, C]) ``([C, C, C, X, X, E]),
  grammar_step ``(XC_CX) ``([a, a, a, M, B, C, B, C, B, C, C, C, C]) ``([C, C, X, X, E]),
  grammar_step ``(XC_CX) ``([a, a, a, M, B, C, B, C, B, C, C, C, C, C]) ``([C, X, X, E]),
  grammar_step ``(XC_CX) ``([a, a, a, M, B, C, B, C, B, C, C, C, C, C, C]) ``([X, X, E]),
  grammar_step ``(CB_BC) ``([a, a, a, M, B]) ``([C, B, C, C, C, C, C, C, C, X, X, X, E]),
  grammar_step ``(CB_BC) ``([a, a, a, M, B, B, C]) ``([C, C, C, C, C, C, C, X, X, X, E]),
  grammar_step ``(CB_BC) ``([a, a, a, M, B, B]) ``([C, C, C, C, C, C, C, C, X, X, X, E]),
  -- a^3.M.B^3.C^9.X^3.E
  apply grammar_deri_of_deri_deri,
  {
    change
      grammar_derives gr_mul
        ([a, a, a, M, B, B, B, C, C, C, C, C, C, C, C, C] ++ [X, X, X, E])
        ([a, a, a, M, B, B, B, C, C, C, C, C, C, C, C, C] ++ [E]),
    apply grammar_derives_with_prefix,
    grammar_step ``(XE_E) ``([X, X]) ``([]),
    grammar_step ``(XE_E) ``([X]) ``([]),
    grammar_step ``(XE_E) ``([]) ``([]),
    apply grammar_deri_self,
  },
  change
    grammar_derives gr_mul
      ([a, a, a] ++ [M, B, B, B, C, C, C, C, C, C, C, C, C, E])
      ([a, a, a] ++ [b, b, b, c, c, c, c, c, c, c, c, c]),
  apply grammar_derives_with_prefix,
  grammar_step ``(MB_bM) ``([]) ``([B, B, C, C, C, C, C, C, C, C, C, E]),
  grammar_step ``(MB_bM) ``([b]) ``([B, C, C, C, C, C, C, C, C, C, E]),
  grammar_step ``(MB_bM) ``([b, b]) ``([C, C, C, C, C, C, C, C, C, E]),
  change
    grammar_derives gr_mul
      ([b, b, b] ++ [M, C, C, C, C, C, C, C, C, C, E])
      ([b, b, b] ++ [c, c, c, c, c, c, c, c, c]),
  apply grammar_derives_with_prefix,
  grammar_step ``(M_K) ``([]) ``([C, C, C, C, C, C, C, C, C, E]),
  grammar_step ``(KC_cK) ``([]) ``([C, C, C, C, C, C, C, C, E]),
  grammar_step ``(KC_cK) ``([c]) ``([C, C, C, C, C, C, C, E]),
  grammar_step ``(KC_cK) ``([c, c]) ``([C, C, C, C, C, C, E]),
  grammar_step ``(KC_cK) ``([c, c, c]) ``([C, C, C, C, C, E]),
  grammar_step ``(KC_cK) ``([c, c, c, c]) ``([C, C, C, C, E]),
  grammar_step ``(KC_cK) ``([c, c, c, c, c]) ``([C, C, C, E]),
  grammar_step ``(KC_cK) ``([c, c, c, c, c, c]) ``([C, C, E]),
  grammar_step ``(KC_cK) ``([c, c, c, c, c, c, c]) ``([C, E]),
  grammar_step ``(KC_cK) ``([c, c, c, c, c, c, c, c]) ``([E]),
  grammar_step ``(KE_nil) ``([c, c, c, c, c, c, c, c, c]) ``([]),
  apply grammar_deri_self,
end


lemma list_repeat_zero {α : Type*} (s : α) :
  list.repeat s 0 = [] :=
begin
  refl,
end

lemma list_repeat_succ_eq_singleton_append {α : Type*} (s : α) (n : ℕ) :
  list.repeat s n.succ = [s] ++ list.repeat s n :=
begin
  -- almost the same as `list.repeat_succ` which is a `rfl` lemma
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
    (list.repeat a m ++ [M] ++ list.repeat X m ++ list.repeat B n ++ [E])
    (list.repeat a m ++ [M] ++ list.repeat B n ++ list.repeat C (m * n) ++
      list.repeat X m ++ [E]) :=
begin
  sorry
end

private lemma steps_XE_E (m n : ℕ) :
  grammar_derives gr_mul
    (list.repeat a m ++ [M] ++ list.repeat B n ++ list.repeat C (m * n) ++ list.repeat X m ++ [E])
    (list.repeat a m ++ [M] ++ list.repeat B n ++ list.repeat C (m * n) ++ [E]) :=
begin
  induction m with k ih,
  {
    rw [list_repeat_zero X, list.append_nil],
    apply grammar_deri_self,
  },
  sorry
end

private lemma steps_MB_bM (m n : ℕ) :
  grammar_derives gr_mul
    (list.repeat a m ++ [M] ++ list.repeat B n ++ list.repeat C (m * n) ++ [E])
    (list.repeat a m ++ list.repeat b n ++ [M] ++ list.repeat C (m * n) ++ [E]) :=
begin
  sorry
end

private lemma steps_KC_cK (m n : ℕ) :
  grammar_derives gr_mul
    (list.repeat a m ++ list.repeat b n ++ [K] ++ list.repeat C (m * n) ++ [E])
    (list.repeat a m ++ list.repeat b n ++ list.repeat c (m * n) ++ [K] ++ [E]) :=
begin
  sorry
end

-- example 3 * 3 = 9 reproved using the new lemmata
example : grammar_generates gr_mul [a_, a_, a_, b_, b_, b_, c_, c_, c_, c_, c_, c_, c_, c_, c_] :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  apply grammar_deri_of_deri_deri (steps_L_aLX 3),
  apply grammar_deri_of_deri_deri (steps_R_BR 3 3),
  grammar_step ``(L_M) ``([a, a, a]) ``([X, X, X, B, B, B, R]),
  grammar_step ``(R_E) ``([a, a, a, M, X, X, X, B, B, B]) ``([]),
  apply grammar_deri_of_deri_deri (steps_quadratic 3 3),
  apply grammar_deri_of_deri_deri (steps_XE_E 3 3),
  apply grammar_deri_of_deri_deri (steps_MB_bM 3 3),
  grammar_step ``(M_K) ``([a, a, a, b, b, b]) ``([C, C, C, C, C, C, C, C, C, E]),
  apply grammar_deri_of_deri_deri (steps_KC_cK 3 3),
  apply grammar_deri_of_tran,
  use KE_nil,
  split,
  {
    find_in_explicit_list,
  },
  use [[a, a, a, b, b, b, c, c, c, c, c, c, c, c, c], []],
  split;
  refl,
end

-- example 7 * 11 = 77
example : grammar_generates gr_mul (list.repeat a_ 7 ++ list.repeat b_ 11 ++ list.repeat c_ 77) :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  apply grammar_deri_of_deri_deri (steps_L_aLX 7),
  apply grammar_deri_of_deri_deri (steps_R_BR 7 11),
  grammar_step ``(L_M) ``(list.repeat a 7) ``(list.repeat X 7 ++ list.repeat B 11 ++ [R]),
  grammar_step ``(R_E) ``(list.repeat a 7 ++ [M] ++ list.repeat X 7 ++ list.repeat B 11) ``([]),
  apply grammar_deri_of_deri_deri (steps_quadratic 7 11),
  apply grammar_deri_of_deri_deri (steps_XE_E 7 11),
  apply grammar_deri_of_deri_deri (steps_MB_bM 7 11),
  grammar_step ``(M_K) ``((list.repeat a 7 ++ list.repeat b 11)) ``(list.repeat C 77 ++ [E]),
  apply grammar_deri_of_deri_deri (steps_KC_cK 7 11),
  apply grammar_deri_of_tran,
  use KE_nil,
  split,
  {
    find_in_explicit_list,
  },
  use [(list.repeat a 7 ++ list.repeat b 11 ++ list.repeat c 77), []],
  split;
  refl,
end


private theorem multiplication_complete (m n : ℕ) :
  grammar_generates gr_mul (list.repeat a_ m ++ list.repeat b_ n ++ list.repeat c_ (m * n)) :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  apply grammar_deri_of_deri_deri (steps_L_aLX m),
  apply grammar_deri_of_deri_deri (steps_R_BR m n),
  apply grammar_deri_of_tran_deri,
  {
    use L_M,
    split,
    {
      find_in_explicit_list,
    },
    use [list.repeat a m, list.repeat X m ++ list.repeat B n ++ [R]],
    split;
    finish,
  },
  apply grammar_deri_of_tran_deri,
  {
    use R_E,
    split,
    {
      find_in_explicit_list,
    },
    use [list.repeat a m ++ [M] ++ list.repeat X m ++ list.repeat B n, []],
    split;
    finish,
  },
  rw ←list.singleton_append,
  repeat {
    rw ←list.append_assoc,
  },
  apply grammar_deri_of_deri_deri (steps_quadratic m n),
  apply grammar_deri_of_deri_deri (steps_XE_E m n),
  apply grammar_deri_of_deri_deri (steps_MB_bM m n),
  apply grammar_deri_of_tran_deri,
  {
    use M_K,
    split,
    {
      find_in_explicit_list,
    },
    use [list.repeat a m ++ list.repeat b n, list.repeat C (m * n) ++ [E]],
    split;
    finish,
  },
  repeat {
    rw ←list.append_assoc,
  },
  apply grammar_deri_of_deri_deri (steps_KC_cK m n),
  apply grammar_deri_of_tran,
  use KE_nil,
  split,
  {
    find_in_explicit_list,
  },
  unfold KE_nil,
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

-- example 3 * 3 = 9 reproved using the new theorem
example : grammar_generates gr_mul [a_, a_, a_, b_, b_, b_, c_, c_, c_, c_, c_, c_, c_, c_, c_] :=
begin
  exact multiplication_complete 3 3,
end

-- example 1001 * 587 = 587587
example : grammar_generates gr_mul (list.repeat a_ 1001 ++ list.repeat b_ 587 ++ list.repeat c_ 587587) :=
begin
  have pe : 587587 = 1001 * 587,
  {
    norm_num,
  },
  rw pe,
  apply multiplication_complete,
end
