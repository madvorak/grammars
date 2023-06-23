import classes.unrestricted.basics.toolbox
import utilities.list_utils
import utilities.written_by_others.trim_assoc


inductive alphabet
| _a : alphabet
| _b : alphabet
| _c : alphabet

inductive inner
| _S : inner
| _L : inner
| _R : inner
| _X : inner
| _B : inner
| _M : inner
| _E : inner
| _C : inner
| _K : inner

private def a_ := alphabet._a
private def b_ := alphabet._b
private def c_ := alphabet._c

private def S_ := inner._S
private def L_ := inner._L
private def R_ := inner._R
private def X_ := inner._X
private def B_ := inner._B
private def M_ := inner._M
private def E_ := inner._E
private def C_ := inner._C
private def K_ := inner._K

private def my_char : Type := symbol alphabet inner

private def a : my_char := symbol.terminal a_
private def b : my_char := symbol.terminal b_
private def c : my_char := symbol.terminal c_

private def S : my_char := symbol.nonterminal S_
private def L : my_char := symbol.nonterminal L_
private def R : my_char := symbol.nonterminal R_
private def X : my_char := symbol.nonterminal X_
private def B : my_char := symbol.nonterminal B_
private def M : my_char := symbol.nonterminal M_
private def E : my_char := symbol.nonterminal E_
private def C : my_char := symbol.nonterminal C_
private def K : my_char := symbol.nonterminal K_

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
CB → BC
XC → CX
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

private def my_rule : Type := grule alphabet inner

private def S_LR   : my_rule := grule.mk  [] S_ [] [L, R]
private def L_aLX  : my_rule := grule.mk  [] L_ [] [a, L, X]
private def R_BR   : my_rule := grule.mk  [] R_ [] [B, R]
private def L_M    : my_rule := grule.mk  [] L_ [] [M]
private def R_E    : my_rule := grule.mk  [] R_ [] [E]
private def XB_BCX : my_rule := grule.mk [X] B_ [] [B, C, X]
private def CB_BC  : my_rule := grule.mk [C] B_ [] [B, C]
private def XC_CX  : my_rule := grule.mk [X] C_ [] [C, X]
private def XE_E   : my_rule := grule.mk [X] E_ [] [E]      -- shortens the word
private def MB_bM  : my_rule := grule.mk [M] B_ [] [b, M]
private def M_K    : my_rule := grule.mk  [] M_ [] [K]
private def KC_cK  : my_rule := grule.mk [K] C_ [] [c, K]
private def KE_nil : my_rule := grule.mk [K] E_ [] []       -- shortens the word

private def gr_mul : grammar alphabet :=
grammar.mk inner S_ [S_LR, L_aLX, R_BR, L_M, R_E, XB_BCX, CB_BC, XC_CX, XE_E, MB_bM, M_K, KC_cK, KE_nil]


private meta def grammar_step (rule : pexpr) (pref post : pexpr) : tactic unit := `[
  apply grammar_deri_of_tran_deri,
  tactic.use [rule],
  split_ile,
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
    apply grammar_deri_with_prefix,
    grammar_step ``(XE_E) ``([X, X]) ``([]),
    grammar_step ``(XE_E) ``([X]) ``([]),
    grammar_step ``(XE_E) ``([]) ``([]),
    apply grammar_deri_self,
  },
  change
    grammar_derives gr_mul
      ([a, a, a] ++ [M, B, B, B, C, C, C, C, C, C, C, C, C, E])
      ([a, a, a] ++ [b, b, b, c, c, c, c, c, c, c, c, c]),
  apply grammar_deri_with_prefix,
  grammar_step ``(MB_bM) ``([]) ``([B, B, C, C, C, C, C, C, C, C, C, E]),
  grammar_step ``(MB_bM) ``([b]) ``([B, C, C, C, C, C, C, C, C, C, E]),
  grammar_step ``(MB_bM) ``([b, b]) ``([C, C, C, C, C, C, C, C, C, E]),
  change
    grammar_derives gr_mul
      ([b, b, b] ++ [M, C, C, C, C, C, C, C, C, C, E])
      ([b, b, b] ++ [c, c, c, c, c, c, c, c, c]),
  apply grammar_deri_with_prefix,
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


private lemma sub_suc_suc {m n : ℕ} (n_lt_m : n < m) : m - n = (m - n.succ).succ :=
begin
  omega,
end

private lemma steps_L_aLX (m : ℕ) :
  grammar_derives gr_mul [L, R] (list.replicate m a ++ [L] ++ list.replicate m X ++ [R]) :=
begin
  induction m with k ih,
  {
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran ih,
  use L_aLX,
  split_ile,
  use [list.replicate k a, list.replicate k X ++ [R]],
  split,
  {
    simp [L, L_aLX, list.append_nil, list.append_assoc],
  },
  {
    rw list.replicate_succ_eq_append_singleton a,
    rw list.replicate_succ_eq_singleton_append X,
    simp [L, L_aLX, list.append_assoc],
  },
end

private lemma steps_R_BR (m n : ℕ) :
  grammar_derives gr_mul
    (list.replicate m a ++ [L] ++ list.replicate m X ++ [R])
    (list.replicate m a ++ [L] ++ list.replicate m X ++ list.replicate n B ++ [R]) :=
begin
  induction n with k ih,
  {
    rw [list.replicate, list.append_nil],
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran ih,
  use R_BR,
  split_ile,
  use [list.replicate m a ++ [L] ++ list.replicate m X ++ list.replicate k B, []],
  split,
  {
    simp [R, R_BR, list.append_nil],
  },
  {
    rw list.replicate_succ_eq_append_singleton B,
    simp [R, R_BR, list.append_nil, list.append_assoc],
  },
end

private lemma steps_quadratic (m n : ℕ) :
  grammar_derives gr_mul
    (list.replicate m a ++ [M] ++ list.replicate m X ++ list.replicate n B ++ [E])
    (list.replicate m a ++ [M] ++ list.replicate n B ++ list.replicate (m * n) C ++
      list.replicate m X ++ [E]) :=
begin
  apply grammar_deri_with_postfix,
  repeat {
    rw list.append_assoc (list.replicate m a ++ [M]),
  },
  apply grammar_deri_with_prefix,

  have parametrized : ∀ q : ℕ, q ≤ m →
    grammar_derives gr_mul
      (list.replicate m X ++ list.replicate n B)
      (list.replicate (m - q) X ++ list.replicate n B ++ list.replicate (q * n) C ++ list.replicate q X),
  {
    intros q q_le_m,
    induction q with k ih,
    {
      rw [nat.sub_zero, zero_mul, list.replicate_zero, list.replicate_zero, list.append_nil, list.append_nil],
      apply grammar_deri_self,
    },
    apply grammar_deri_of_deri_deri (ih (nat.le_of_succ_le q_le_m)),

    have big_step_generateCs :
      grammar_derives gr_mul
        (list.replicate (m - k) X ++ list.replicate n B ++ list.replicate (k * n) C ++ list.replicate k X)
        (list.replicate (m - k.succ) X ++ [B, C] ^^ n ++ [X] ++ list.replicate (k * n) C ++ list.replicate k X),
    {
      apply grammar_deri_with_postfix,
      apply grammar_deri_with_postfix,

      have aux_generateCs : ∀ p : ℕ, p ≤ n →
        grammar_derives gr_mul
          (list.replicate (m - k) X ++ list.replicate n B)
          (list.replicate (m - k.succ) X ++ [B, C] ^^ p ++ [X] ++ list.replicate (n - p) B),
      {
        intros p p_le_n,
        induction p with r ih,
        {
          rw nat.sub_zero,
          unfold list.n_times,
          rw list.replicate_zero,
          rw list.join,
          rw list.append_nil,
          rw ←list.replicate_succ_eq_append_singleton,
          rw ←sub_suc_suc, swap,
          {
            rwa nat.succ_le_iff at q_le_m,
          },
          apply grammar_deri_self,
        },
        apply grammar_deri_of_deri_tran (ih (nat.le_of_succ_le p_le_n)),
        use XB_BCX,
        split_ile,
        use list.replicate (m - k.succ) X ++ [B, C] ^^ r,
        use list.replicate (n - r.succ) B,
        split,
        {
          repeat {
            rw list.append_assoc,
          },
          trim,
          have r_lt_n : r < n,
          {
            rwa nat.succ_le_iff at p_le_n,
          },
          rw sub_suc_suc r_lt_n,
          rw list.replicate_succ_eq_singleton_append B,
          repeat {
            rw ←list.append_assoc,
          },
          refl,
        },
        {
          trim,
          unfold list.n_times,
          rw list.replicate_succ_eq_append_singleton,
          rw list.join_append,
          finish,
        },
      },
      have generatedCs := aux_generateCs n (by refl),
      rwa [nat.sub_self, list.replicate_zero, list.append_nil] at generatedCs,
    },
    apply grammar_deri_of_deri_deri big_step_generateCs,
    clear big_step_generateCs,

    have big_step_bubbleCs :
      grammar_derives gr_mul
        (list.replicate (m - k.succ) X ++ [B, C] ^^ n ++ [X] ++ list.replicate (k * n) C ++ list.replicate k X)
        (list.replicate (m - k.succ) X ++ list.replicate n B ++ list.replicate n C ++ [X] ++
          list.replicate (k * n) C ++ list.replicate k X),
    {
      apply grammar_deri_with_postfix,
      apply grammar_deri_with_postfix,
      apply grammar_deri_with_postfix,
      rw list.append_assoc,
      apply grammar_deri_with_prefix,

      have aux_bubbleCs : ∀ s : ℕ, s ≤ n →
        grammar_derives gr_mul
          ([B, C] ^^ n)
          (list.replicate s B ++ list.replicate s C ++ [B, C] ^^ (n - s)),
      {
        intros s s_le_n,
        induction s with z ih,
        {
          rw list.replicate_zero,
          rw list.nil_append,
          rw list.replicate_zero,
          rw list.nil_append,
          rw nat.sub_zero,
          apply grammar_deri_self,
        },
        apply grammar_deri_of_deri_deri (ih (nat.le_of_succ_le s_le_n)),
        have z_lt_n : z < n,
        {
          rwa nat.succ_le_iff at s_le_n,
        },
        rw sub_suc_suc z_lt_n,
        unfold list.n_times,
        rw list.replicate_succ_eq_singleton_append,
        rw list.join_append,
        rw list.join_singleton,
        repeat {
          rw ←list.append_assoc,
        },
        apply grammar_deri_with_postfix,
        rw list.replicate_succ_eq_append_singleton B,
        rw list.append_assoc,
        rw list.append_assoc,
        apply grammar_deri_with_prefix,
        rw list.replicate_succ_eq_append_singleton C,
        convert_to
          grammar_derives gr_mul
            (list.replicate z C ++ [B] ++ [C])
            ([B] ++ list.replicate z C ++ [C]),
        {
          rw list.append_assoc,
          refl,
        },
        apply grammar_deri_with_postfix,

        have aux_bubbleB : ∀ x : ℕ, x ≤ z →
          grammar_derives gr_mul
            (list.replicate z C ++ [B])
            (list.replicate (z - x) C ++ [B] ++ list.replicate x C),
        {
          intros x x_le_z,
          induction x with y ih,
          {
            rw [nat.sub_zero, list.replicate_zero, list.append_nil],
            apply grammar_deri_self,
          },
          apply grammar_deri_of_deri_tran (ih (nat.le_of_succ_le x_le_z)),
          use CB_BC,
          split_ile,
          use [list.replicate (z - y.succ) C, list.replicate y C],
          split,
          {
            trim,
            have y_lt_z : y < z,
            {
              rwa nat.succ_le_iff at x_le_z,
            },
            rw sub_suc_suc y_lt_z,
            rw list.replicate_succ_eq_append_singleton C,
            repeat {
              rw list.append_assoc,
            },
            refl,
          },
          {
            rw list.replicate_succ_eq_singleton_append C,
            rw ←list.append_assoc,
            trim,
          },
        },
        have bubbledB := aux_bubbleB z (by refl),
        rwa [nat.sub_self, list.replicate_zero, list.nil_append] at bubbledB,
      },
      have bubbledCs := aux_bubbleCs n (by refl),
      rw nat.sub_self at bubbledCs,
      unfold list.n_times at bubbledCs,
      rw list.append_assoc at bubbledCs,
      rw list.replicate_zero at bubbledCs,
      rw list.join at bubbledCs,
      rwa list.append_nil at bubbledCs,
    },
    apply grammar_deri_of_deri_deri big_step_bubbleCs,
    clear big_step_bubbleCs,

    repeat {
      rw list.append_assoc,
    },
    apply grammar_deri_with_prefix,
    apply grammar_deri_with_prefix,
    rw nat.succ_mul,
    rw add_comm,
    rw list.replicate_add,
    rw list.append_assoc,
    apply grammar_deri_with_prefix,
    rw list.replicate_succ_eq_singleton_append X,
    repeat {
      rw ←list.append_assoc,
    },
    apply grammar_deri_with_postfix,

    have skipCs : ∀ d e : ℕ, d ≤ e →
      grammar_derives gr_mul
        ([X] ++ list.replicate e C)
        (list.replicate d C ++ [X] ++ list.replicate (e - d) C),
    {
      intros d e d_le_e,
      induction d with f ih,
      {
        apply grammar_deri_self,
      },
      apply grammar_deri_of_deri_tran (ih (nat.le_of_succ_le d_le_e)),
      use XC_CX,
      split_ile,
      use [list.replicate f C, list.replicate (e - f.succ) C],
      split,
      {
        have f_lt_e : f < e,
        {
          rwa nat.succ_le_iff at d_le_e,
        },
        rw sub_suc_suc f_lt_e,
        rw list.replicate_succ_eq_singleton_append C,
        rw ←list.append_assoc,
        trim,
      },
      {
        rw list.replicate_succ_eq_append_singleton C,
        trim,
        rw list.append_assoc,
        refl,
      },
    },
    have almost := skipCs (k * n) (k * n) (by refl),
    rwa [nat.sub_self, list.replicate_zero, list.append_nil] at almost,
  },
  convert parametrized m (by refl),
  rw [nat.sub_self, list.replicate_zero, list.nil_append],
end

private lemma steps_XE_E (m n : ℕ) :
  grammar_derives gr_mul
    (list.replicate m a ++ [M] ++ list.replicate n B ++ list.replicate (m * n) C ++ list.replicate m X ++ [E])
    (list.replicate m a ++ [M] ++ list.replicate n B ++ list.replicate (m * n) C ++ [E]) :=
begin
  have backwards : ∀ q : ℕ, q ≤ m →
    grammar_derives gr_mul
      (list.replicate m a ++ [M] ++ list.replicate n B ++ list.replicate (m * n) C ++ list.replicate m X ++ [E])
      (list.replicate m a ++ [M] ++ list.replicate n B ++ list.replicate (m * n) C ++ list.replicate (m - q) X ++ [E]),
  {
    intros q ass,
    induction q with k ih,
    {
      apply grammar_deri_self,
    },
    apply grammar_deri_of_deri_tran (ih (nat.le_of_succ_le ass)),
    use XE_E,
    split_ile,
    use [
      list.replicate m a ++ [M] ++ list.replicate n B ++ list.replicate (m * n) C ++ list.replicate (m - k.succ) X,
      []
    ],
    split,
    {
      have detach_X : list.replicate (m - k) X = list.replicate (m - k.succ) X ++ [X],
      {
        have k_lt_m : k < m,
        {
          rwa nat.succ_le_iff at ass,
        },
        rw sub_suc_suc k_lt_m,
        apply list.replicate_succ_eq_append_singleton,
      },
      rw detach_X,
      finish,
    },
    {
      rw list.append_nil,
      refl,
    },
  },
  have almost := backwards m (by refl),
  rwa [nat.sub_self, list.replicate_zero, list.append_nil] at almost,
end

private lemma steps_MB_bM (m n : ℕ) :
  grammar_derives gr_mul
    (list.replicate m a ++ [M] ++ list.replicate n B ++ list.replicate (m * n) C ++ [E])
    (list.replicate m a ++ list.replicate n b ++ [M] ++ list.replicate (m * n) C ++ [E]) :=
begin
  apply grammar_deri_with_postfix,
  apply grammar_deri_with_postfix,
  rw list.append_assoc,
  rw list.append_assoc,
  apply grammar_deri_with_prefix,

  have bees : ∀ k : ℕ, k ≤ n →
    grammar_derives gr_mul ([M] ++ list.replicate n B) (list.replicate k b ++ [M] ++ list.replicate (n - k) B),
  {
    intros k ass,
    induction k with q ih,
    {
      apply grammar_deri_self,
    },
    apply grammar_deri_of_deri_tran (ih (nat.le_of_succ_le ass)),
    use MB_bM,
    split_ile,
    use [list.replicate q b, list.replicate (n - q.succ) B],
    split,
    {
      have q_lt_n : q < n,
      {
        rwa nat.succ_le_iff at ass,
      },
      rw sub_suc_suc q_lt_n,
      rw list.replicate_succ_eq_singleton_append,
      repeat {
        rw list.append_assoc,
      },
      trim,
    },
    {
      rw list.replicate_succ_eq_append_singleton b,
      trim,
      rw list.append_assoc,
      refl,
    },
  },
  have almost := bees n (by refl),
  rwa [nat.sub_self, list.replicate_zero, list.append_nil] at almost,
end

private lemma steps_KC_cK (m n : ℕ) :
  grammar_derives gr_mul
    (list.replicate m a ++ list.replicate n b ++ [K] ++ list.replicate (m * n) C ++ [E])
    (list.replicate m a ++ list.replicate n b ++ list.replicate (m * n) c ++ [K] ++ [E]) :=
begin
  apply grammar_deri_with_postfix,
  repeat {
    rw list.append_assoc,
  },
  apply grammar_deri_with_prefix,
  apply grammar_deri_with_prefix,

  have terminating : ∀ p q : ℕ, p ≤ q →
    grammar_derives gr_mul ([K] ++ list.replicate q C) (list.replicate p c ++ [K] ++ list.replicate (q - p) C),
  {
    intros p q ass,
    induction p with r ih,
    {
      apply grammar_deri_self,
    },
    apply grammar_deri_of_deri_tran (ih (nat.le_of_succ_le ass)),
    clear ih,
    use KC_cK,
    split_ile,
    use [list.replicate r c, list.replicate (q - r.succ) C],
    split,
    {
      have r_lt_q : r < q,
      {
        rwa nat.succ_le_iff at ass,
      },
      rw sub_suc_suc r_lt_q,
      rw list.replicate_succ_eq_singleton_append,
      repeat {
        rw list.append_assoc,
      },
      trim,
    },
    {
      rw list.replicate_succ_eq_append_singleton c,
      trim,
      rw list.append_assoc,
      refl,
    },
  },
  have almost := terminating (m * n) (m * n) (by refl),
  rwa [nat.sub_self, list.replicate_zero, list.append_nil] at almost,
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
  split_ile,
  use [[a, a, a, b, b, b, c, c, c, c, c, c, c, c, c], []],
  split;
  refl,
end

-- example 7 * 11 = 77
example : grammar_generates gr_mul (list.replicate 7 a_ ++ list.replicate 11 b_ ++ list.replicate 77 c_) :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  apply grammar_deri_of_deri_deri (steps_L_aLX 7),
  apply grammar_deri_of_deri_deri (steps_R_BR 7 11),
  grammar_step ``(L_M) ``(list.replicate 7 a) ``(list.replicate 7 X ++ list.replicate 11 B ++ [R]),
  grammar_step ``(R_E) ``(list.replicate 7 a ++ [M] ++ list.replicate 7 X ++ list.replicate 11 B) ``([]),
  apply grammar_deri_of_deri_deri (steps_quadratic 7 11),
  apply grammar_deri_of_deri_deri (steps_XE_E 7 11),
  apply grammar_deri_of_deri_deri (steps_MB_bM 7 11),
  grammar_step ``(M_K) ``((list.replicate 7 a ++ list.replicate 11 b)) ``(list.replicate 77 C ++ [E]),
  apply grammar_deri_of_deri_deri (steps_KC_cK 7 11),
  apply grammar_deri_of_tran,
  use KE_nil,
  split_ile,
  use [(list.replicate 7 a ++ list.replicate 11 b ++ list.replicate 77 c), []],
  split;
  refl,
end


private theorem multiplication_complete (m n : ℕ) :
  grammar_generates gr_mul (list.replicate m a_ ++ list.replicate n b_ ++ list.replicate (m * n) c_) :=
begin
  grammar_step ``(S_LR) ``([]) ``([]),
  apply grammar_deri_of_deri_deri (steps_L_aLX m),
  apply grammar_deri_of_deri_deri (steps_R_BR m n),
  apply grammar_deri_of_tran_deri,
  {
    use L_M,
    split_ile,
    use [list.replicate m a, list.replicate m X ++ list.replicate n B ++ [R]],
    split;
    finish,
  },
  apply grammar_deri_of_tran_deri,
  {
    use R_E,
    split_ile,
    use [list.replicate m a ++ [M] ++ list.replicate m X ++ list.replicate n B, []],
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
    split_ile,
    use [list.replicate m a ++ list.replicate n b, list.replicate (m * n) C ++ [E]],
    split;
    finish,
  },
  repeat {
    rw ←list.append_assoc,
  },
  apply grammar_deri_of_deri_deri (steps_KC_cK m n),
  apply grammar_deri_of_tran,
  use KE_nil,
  split_ile,
  unfold KE_nil,
  use [(list.replicate m a ++ list.replicate n b ++ list.replicate (m * n) c), []],
  split,
  {
    finish,
  },
  rw list.map_append_append,
  repeat {
    rw list.map_replicate,
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
example : grammar_generates gr_mul (list.replicate 1001 a_ ++ list.replicate 587 b_ ++ list.replicate 587587 c_) :=
begin
  have pe : 587587 = 1001 * 587,
  {
    norm_num,
  },
  rw pe,
  apply multiplication_complete,
end
