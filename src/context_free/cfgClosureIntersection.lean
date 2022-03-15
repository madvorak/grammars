import context_free.cfgClosureConcatenation
import context_free.cfgClosurePermutation
import context_free.cfgPumping
import tactic


section reusable_defs_and_lemmata
variables {α : Type} [decidable_eq α]

def count_in (w : list α) (a : α) : ℕ :=
list.sum (list.map (λ x, ite (x = a) 1 0) w)

lemma count_in_repeat_eq (a : α) (n : ℕ) :
  count_in (list.repeat a n) a  =  n  :=
begin
  sorry,
end

lemma count_in_repeat_neq {a : α} {b : α} (h : a ≠ b) (n : ℕ) :
  count_in (list.repeat a n) b  =  0  :=
begin
  sorry,
end

lemma count_in_append (w₁ w₂ : list α) (a : α) :
  count_in (w₁ ++ w₂) a  =  count_in w₁ a  +  count_in w₂ a  :=
begin
  rw count_in,
  rw list.map_append,
  rw list.sum_append,
  refl,
end

lemma count_in_le_length {w : list α} {a : α} :
  count_in w a ≤ w.length :=
-- maybe not be needed in the end
begin
  rw count_in,
  have upper_bound : ∀ y : α, (λ (x : α), ite (x = a) 1 0) y ≤ 1,
  {
    intro z,
    simp,
    by_cases (z = a),
    {
      rw h,
      simp,
    },
    {
      convert_to ite false 1 0 ≤ 1;
      simp,
      exact h,
    },
  },
  calc (list.map (λ (x : α), ite (x = a) 1 0) w).sum
      ≤ (list.map (λ (x : α), 1) w).sum : sorry
  ... ≤ 1 * w.length                    : sorry
  ... = w.length                        : by rw one_mul,
end

lemma count_in_pos_of_in {w : list α} {a : α} (h : a ∈ w) :
  count_in w a > 0 :=
begin
  by_contradiction contr,
  rw not_lt at contr,
  rw nat.le_zero_iff at contr,
  sorry,
end

lemma count_in_zero_of_notin {w : list α} {a : α} (h : a ∉ w) :
  count_in w a = 0 :=
begin
  sorry,
end

end reusable_defs_and_lemmata


section specific_defs_and_lemmata

private def a_ : fin 3 := 0
private def b_ : fin 3 := 1
private def c_ : fin 3 := 2

private def a : symbol (fin 3) (fin 1) := symbol.terminal a_
private def b : symbol (fin 3) (fin 1) := symbol.terminal b_
private def c : symbol (fin 3) (fin 1) := symbol.terminal c_

private def lang_eq_any : language (fin 3) :=
λ w, ∃ n m : ℕ, w = list.repeat a_ n ++ list.repeat b_ n ++ list.repeat c_ m

private def lang_any_eq : language (fin 3) :=
λ w, ∃ n m : ℕ, w = list.repeat a_ n ++ list.repeat b_ m ++ list.repeat c_ m

private def lang_eq_eq : language (fin 3) :=
λ w, ∃ n : ℕ, w = list.repeat a_ n ++ list.repeat b_ n ++ list.repeat c_ n


section what_is_CF

section not_CF

private lemma false_of_uvvxyyz {_a _b _c : fin 3} {n : ℕ} {u v x y z: list (fin 3)}
  (elimin : ∀ s : fin 3,  s ≠ _a  →  s ≠ _b  →  s ≠ _c  → false)
  (no_a: _a ∉ v ++ y) (nonempty: (v ++ y).length > 0)
  (counts_ab: ∀ (w : list (fin 3)), w ∈ lang_eq_eq → count_in w _a = count_in w _b)
  (counts_ac: ∀ (w : list (fin 3)), w ∈ lang_eq_eq → count_in w _a = count_in w _c)
  (counted_a : count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _a = n + 1 + count_in (v ++ y) _a)
  (counted_b : count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _b = n + 1 + count_in (v ++ y) _b)
  (counted_c : count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _c = n + 1 + count_in (v ++ y) _c)
  (pumping: u ++ v ^ 2 ++ x ++ y ^ 2 ++ z ∈ lang_eq_eq) :
    false :=
begin
  have extra_not_a : _b ∈ (v ++ y) ∨ _c ∈ (v ++ y),
  {
    let first_letter := (v ++ y).nth_le 0 nonempty,

    have first_letter_b_or_c : first_letter = _b ∨ first_letter = _c,
    {
      have first_letter_not_a : first_letter ≠ _a,
      {
        by_contradiction contra,
        have yes_a : _a ∈ v ++ y,
        {
          rw ← contra,
          apply list.nth_le_mem,
        },
        exact no_a yes_a,
      },
      by_contradiction contr,
      push_neg at contr,
      cases contr with first_letter_not_b first_letter_not_c,
      exact elimin ((v ++ y).nth_le 0 nonempty)
                   first_letter_not_a first_letter_not_b first_letter_not_c,
    },
    cases first_letter_b_or_c with first_letter_b first_letter_c,
    {
      left,
      rw ← first_letter_b,
      apply list.nth_le_mem,
    },
    {
      right,
      rw ← first_letter_c,
      apply list.nth_le_mem,
    },
  },
  have hab := counts_ab (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) pumping,
  have hac := counts_ac (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) pumping,

  cases pumping with n' pump',
  have count_a : count_in (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) _a = n + 1,
  {
    unfold list_n_times,
    simp [- list.append_assoc],
    repeat { rw count_in_append },
    have rearrange :
      count_in u _a + (count_in v _a + count_in v _a) + count_in x _a + (count_in y _a + count_in y _a) + count_in z _a =
      (count_in u _a + count_in v _a + count_in x _a + count_in y _a + count_in z _a) + (count_in v _a + count_in y _a),
    {
      ring,
    },
    have zero_in_v : count_in v _a = 0,
    {
      rw list.mem_append at no_a,
      push_neg at no_a,
      exact count_in_zero_of_notin no_a.left,
    },
    have zero_in_y : count_in y _a = 0,
    {
      rw list.mem_append at no_a,
      push_neg at no_a,
      exact count_in_zero_of_notin no_a.right,
    },
    rw rearrange,
    repeat { rw ← count_in_append },
    rw counted_a,
    rw count_in_append,
    rw zero_in_v,
    rw zero_in_y,
  },
  
  cases extra_not_a with extra_b extra_c,
  {
    have count_b : count_in (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) _b > n + 1,
    {
      unfold list_n_times,
      simp [- list.append_assoc],
      repeat { rw count_in_append },
      have big_equality :
        count_in u _b + (count_in v _b + count_in v _b) + count_in x _b + (count_in y _b + count_in y _b) + count_in z _b =
        (count_in u _b + count_in v _b + count_in x _b + count_in y _b + count_in z _b) + (count_in v _b + count_in y _b),
      {
        ring,
      },
      rw big_equality,
      repeat { rw ← count_in_append },
      rw counted_b,
      have at_least_one_b : count_in (v ++ y) _b > 0,
      {
        exact count_in_pos_of_in extra_b,
      },
      linarith,
    },
    rw count_a at hab,
    rw hab at count_b,
    exact has_lt.lt.false count_b,
  },
  {
    have count_c : count_in (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) _c > n + 1,
    {
      unfold list_n_times,
      simp [- list.append_assoc],
      repeat { rw count_in_append },
      have big_equality :
        count_in u _c + (count_in v _c + count_in v _c) + count_in x _c + (count_in y _c + count_in y _c) + count_in z _c =
        (count_in u _c + count_in v _c + count_in x _c + count_in y _c + count_in z _c) + (count_in v _c + count_in y _c),
      {
        ring,
      },
      rw big_equality,
      repeat { rw ← count_in_append },
      rw counted_c,
      have at_least_one_c : count_in (v ++ y) _c > 0,
      {
        exact count_in_pos_of_in extra_c,
      },
      linarith,
    },
    rw count_a at hac,
    rw hac at count_c,
    exact has_lt.lt.false count_c,
  },
end

private lemma notCF_lang_eq_eq : ¬ is_CF lang_eq_eq :=
begin
  intro h,

  have pum := CF_pumping h,
  cases pum with n pump,
  specialize pump (list.repeat a_ (n+1) ++ list.repeat b_ (n+1) ++ list.repeat c_ (n+1)),
  specialize pump (by { use n + 1, }) (by {
    rw list.length_append,
    rw list.length_repeat,
    calc (list.repeat a_ (n + 1) ++ list.repeat b_ (n + 1)).length + (n + 1)
        ≥ n + 1 : le_add_self
    ... ≥ n     : nat.le_succ n,
  }),
  rcases pump with ⟨ u, v, x, y, z, concatenating, nonempty, vxy_short, pumping ⟩,
  specialize pumping 2,

  have neq_ab : a_ ≠ b_,
  {
    dec_trivial,
  },
  have neq_ac : a_ ≠ c_,
  {
    dec_trivial,
  },
  have neq_bc : b_ ≠ c_,
  {
    dec_trivial,
  },
  have neq_ba := neq_ab.symm,
  have neq_ca := neq_ac.symm,
  have neq_cb := neq_bc.symm,

  have not_all_letters : a_ ∉ (v ++ y) ∨ b_ ∉ (v ++ y) ∨ c_ ∉ (v ++ y),
  {
    by_contradiction contr,
    push_neg at contr,
    rcases contr with ⟨ hva, -, hvc ⟩,

    have vxy_long : (v ++ x ++ y).length > n,
    {
      by_contradiction contr,
      push_neg at contr,

      have total_length_exactly : u.length + (v ++ x ++ y).length + z.length = 3 * n + 3,
      {
        have total_length := congr_arg list.length concatenating,
        repeat { rw list.length_append at total_length },
        repeat { rw list.length_repeat at total_length },
        ring_nf at total_length,
        rw ← add_assoc x.length at total_length,
        rw ← add_assoc v.length at total_length,
        rw ← add_assoc v.length at total_length,
        rw ← add_assoc u.length at total_length,
        rw ← list.length_append at total_length,
        rw ← list.length_append at total_length,
        exact total_length.symm,
      },

      have u_short : u.length ≤ n,
      {
        -- in contradiction with `hva: a_ ∈ v ++ y`
        by_contradiction u_too_much,
        push_neg at u_too_much,

        have relaxed_a : a_ ∈ v ++ x ++ y ++ z,
        {
          cases (list.mem_append.1 hva) with a_in_v a_in_y,
          {
            rw list.append_assoc,
            rw list.append_assoc,
            rw list.mem_append,
            left,
            exact a_in_v,
          },
          {
            have a_in_yz : a_ ∈ y ++ z,
            {
              rw list.mem_append,
              left,
              exact a_in_y,
            },
            rw list.append_assoc,
            rw list.mem_append,
            right,
            exact a_in_yz,
          },
        },
        repeat { rw list.append_assoc at concatenating },
        rcases list.nth_le_of_mem relaxed_a with ⟨ nₐ, hnₐ, h_nthₐ ⟩,
        have h_borrow : ∃ proofoo, (v ++ x ++ y ++ z).nth_le ((nₐ + u.length) - u.length) proofoo = a_,
        {
          rw nat.add_sub_cancel nₐ u.length,
          use hnₐ,
          exact h_nthₐ,
        },
        cases h_borrow with h_nth_a_pr h_nth_a,
        have lt_len : (nₐ + u.length) < (u ++ (v ++ x ++ y ++ z)).length,
        {
          rw list.length_append,
          linarith,
        },
        rw ← list.nth_le_append_right le_add_self lt_len at h_nth_a,

        have orig_nth_le_eq_a : ∃ proofoo, (list.repeat a_ (n + 1) ++ (list.repeat b_ (n + 1) ++ list.repeat c_ (n + 1))).nth_le (nₐ + u.length) proofoo = a_,
        {
          have rebracket : u ++ (v ++ (x ++ (y ++ z))) = u ++ (v ++ x ++ y ++ z),
          {
            simp only [ list.append_assoc ],
          },
          rw concatenating,
          rw rebracket,
          use lt_len,
          exact h_nth_a,
        },
        cases orig_nth_le_eq_a with rrr_nth_le_eq_a_pr rrr_nth_le_eq_a,

        rw @list.nth_le_append_right (fin 3) (list.repeat a_ (n + 1)) (list.repeat b_ (n + 1) ++ list.repeat c_ (n + 1)) (nₐ + u.length) (by {
          rw list.length_repeat,
          calc n + 1 ≤ u.length      : u_too_much
               ...   ≤ nₐ + u.length : le_add_self,
        }) (by {
          rw concatenating,
          rw ← list.append_assoc x,
          rw ← list.append_assoc v,
          rw ← list.append_assoc v,
          exact lt_len,
        }) at rrr_nth_le_eq_a,
        
        have a_in_rb_rc : a_ ∈ (list.repeat b_ (n + 1) ++ list.repeat c_ (n + 1)),
        {
          rw ← rrr_nth_le_eq_a,
          apply list.nth_le_mem,
        },
        rw list.mem_append at a_in_rb_rc,
        cases a_in_rb_rc,
        {
          rw list.mem_repeat at a_in_rb_rc,
          exact neq_ab a_in_rb_rc.right,
        },
        {
          rw list.mem_repeat at a_in_rb_rc,
          exact neq_ac a_in_rb_rc.right,
        },
      },

      have z_short : z.length ≤ n,
      {
        have our_bound : 2 * n + 2 < (u ++ v ++ x ++ y).length,
        {
          have relaxed_c : c_ ∈ u ++ v ++ x ++ y,
          {
            cases (list.mem_append.1 hvc) with c_in_v c_in_y,
            {
              have c_in_uv : c_ ∈ u ++ v,
              {
                rw list.mem_append,
                right,
                exact c_in_v,
              },
              rw list.append_assoc,
              rw list.mem_append,
              left,
              exact c_in_uv,
            },
            {
              rw list.mem_append,
              right,
              exact c_in_y,
            },
          },

          repeat { rw list.append_assoc at concatenating },
          rcases list.nth_le_of_mem relaxed_c with ⟨ m, hm, mth_is_c ⟩,

          have m_big : m ≥ 2 * n + 2,
          {
            have orig_mth_is_c : ∃ proofoo, ((list.repeat a_ (n + 1) ++ list.repeat b_ (n + 1)) ++ list.repeat c_ (n + 1)).nth_le m proofoo = c_,
            {
              repeat { rw ← list.append_assoc at concatenating },
              rw concatenating,
              have m_small : m < (u ++ v ++ x ++ y ++ z).length,
              {
                rw list.length_append,
                linarith,
              },
              rw ← @list.nth_le_append _ _ z m m_small at mth_is_c,
              use m_small,
              exact mth_is_c,
            },
            cases orig_mth_is_c with trash mth_is_c,

            by_contradiction mle,
            push_neg at mle,
            have m_lt_len : m < (list.repeat a_ (n + 1) ++ list.repeat b_ (n + 1)).length,
            {
              rw list.length_append,
              rw list.length_repeat,
              rw list.length_repeat,
              ring_nf,
              exact mle,
            },

            rw list.nth_le_append _ m_lt_len at mth_is_c,
            {
              have c_in_ra_rb : c_ ∈ (list.repeat a_ (n + 1) ++ list.repeat b_ (n + 1)),
              {
                rw ← mth_is_c,
                apply list.nth_le_mem,
              },
              rw list.mem_append at c_in_ra_rb,
              cases c_in_ra_rb with c_in_ra c_in_rb,
              {
                rw list.mem_repeat at c_in_ra,
                exact neq_ca c_in_ra.right,
              },
              {
                rw list.mem_repeat at c_in_rb,
                exact neq_cb c_in_rb.right,
              },
            },
          },

          linarith,
        },

        rw ← list.length_append at total_length_exactly,
        rw ← list.append_assoc at total_length_exactly,
        rw ← list.append_assoc at total_length_exactly,
        linarith,
      },

      linarith,
    },

    exact not_le_of_gt vxy_long vxy_short,
  },

  have counts_ab : ∀ w ∈ lang_eq_eq, count_in w a_ = count_in w b_,
  {
    intros w w_in,
    cases w_in with w_n w_prop,
    rw w_prop,
    repeat { rw count_in_append },
    rw count_in_repeat_neq neq_ab,
    rw count_in_repeat_neq neq_ba,
    rw count_in_repeat_neq neq_ca,
    rw count_in_repeat_neq neq_cb,
    rw count_in_repeat_eq a_,
    rw count_in_repeat_eq b_,
    repeat { rw add_zero },
    rw zero_add,
  },
  have counts_ac : ∀ w ∈ lang_eq_eq, count_in w a_ = count_in w c_,
  {
    intros w w_in,
    cases w_in with w_n w_prop,
    rw w_prop,
    repeat { rw count_in_append },
    rw count_in_repeat_neq neq_ac,
    rw count_in_repeat_neq neq_ca,
    rw count_in_repeat_neq neq_ba,
    rw count_in_repeat_neq neq_bc,
    rw count_in_repeat_eq a_,
    rw count_in_repeat_eq c_,
    repeat { rw add_zero },
    rw zero_add,
  },
  have counts_bc : ∀ w ∈ lang_eq_eq, count_in w b_ = count_in w c_,
  {
    intros w w_in,
    rw ← counts_ab w w_in,
    exact counts_ac w w_in,
  },
  have counts_ba : ∀ w ∈ lang_eq_eq, count_in w b_ = count_in w a_,
  {
    intros w w_in,
    symmetry,
    exact counts_ab w w_in,
  },
  have counts_ca : ∀ w ∈ lang_eq_eq, count_in w c_ = count_in w a_,
  {
    intros w w_in,
    symmetry,
    exact counts_ac w w_in,
  },
  have counts_cb : ∀ w ∈ lang_eq_eq, count_in w c_ = count_in w b_,
  {
    intros w w_in,
    symmetry,
    exact counts_bc w w_in,
  },

  have counted_letter : ∀ s, count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) s =
      count_in (list.repeat a_ (n+1)) s + count_in (list.repeat b_ (n+1)) s + count_in (list.repeat c_ (n+1)) s + count_in (v ++ y) s,
  {
    intro s,
    rw ← concatenating,
    repeat { rw count_in_append },
  },
  have counted_a : count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) a_ = n + 1 + count_in (v ++ y) a_,
  {
    rw counted_letter,
    rw count_in_repeat_eq a_,
    rw count_in_repeat_neq neq_ba,
    rw count_in_repeat_neq neq_ca,
  },
  have counted_b : count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) b_ = n + 1 + count_in (v ++ y) b_,
  {
    rw counted_letter,
    rw count_in_repeat_eq b_,
    rw count_in_repeat_neq neq_cb,
    rw count_in_repeat_neq neq_ab,
    rw zero_add,
  },
  have counted_c : count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) c_ = n + 1 + count_in (v ++ y) c_,
  {
    rw counted_letter,
    rw count_in_repeat_eq c_,
    rw count_in_repeat_neq neq_ac,
    rw count_in_repeat_neq neq_bc,
    rw zero_add,
  },

  have elimin_abc : ∀ s : fin 3,  s ≠ a_  →  s ≠ b_  →  s ≠ c_  → false,
  {
    intros s hsa hsb hsc,
    fin_cases s,
    {
      rw a_ at hsa,
      exact hsa rfl,
    },
    {
      rw b_ at hsb,
      exact hsb rfl,
    },
    {
      rw c_ at hsc,
      exact hsc rfl,
    },
  },
  
  cases not_all_letters with no_a foo,
  {
    exact false_of_uvvxyyz elimin_abc no_a nonempty counts_ab counts_ac
                           counted_a counted_b counted_c pumping,
  },
  cases foo with no_b no_c,
  {
    have elimin_bca : ∀ s : fin 3,  s ≠ b_  →  s ≠ c_  →  s ≠ a_  → false,
    {
      intros s hsb hsc hsa,
      exact elimin_abc s hsa hsb hsc,
    },
    exact false_of_uvvxyyz elimin_bca no_b nonempty counts_bc counts_ba
                           counted_b counted_c counted_a pumping,
  },
  {
    have elimin_cab : ∀ s : fin 3,  s ≠ c_  →  s ≠ a_  →  s ≠ b_  → false,
    {
      intros s hsc hsa hsb,
      exact elimin_abc s hsa hsb hsc,
    },
    exact false_of_uvvxyyz elimin_cab no_c nonempty counts_ca counts_cb
                           counted_c counted_a counted_b pumping,
  },
end

end not_CF


section yes_CF

private def lang_aux_ab : language (fin 3) :=
λ w, ∃ n : ℕ, w = list.repeat a_ n ++ list.repeat b_ n

private lemma CF_lang_aux_ab : is_CF lang_aux_ab :=
sorry

private def lang_aux_c : language (fin 3) :=
λ w, ∃ n : ℕ, w = list.repeat c_ n

private lemma CF_lang_aux_c : is_CF lang_aux_c :=
begin
  use cfg_symbol_star c_,
  apply set.eq_of_subset_of_subset,
  {

    sorry,
  },
  {
    intros w hw,
    cases hw with n hwn,
    rw hwn,
    change CF_generates_str (cfg_symbol_star c_) (list.map symbol.terminal (list.repeat c_ n)),
    convert_to CF_generates_str (cfg_symbol_star c_) (list.repeat c n),
    {
      rw list.map_repeat,
      rw c,
    },
    unfold CF_generates_str,
    clear hwn w,
    have comes_to : CF_derives (cfg_symbol_star c_)
                               [symbol.nonterminal (cfg_symbol_star c_).initial]
                               (list.repeat c n ++ [symbol.nonterminal (0 : fin 1)]),
    {
      induction n with n ih,
      {
        sorry,
      },
      
      sorry,
    },
    apply CF_deri_of_deri_tran comes_to,
    use ((0 : fin 1), []),
    split,
      sorry,
    use [list.repeat c n, []],
    split;
    simp,
  }
end

private lemma CF_lang_eq_any : is_CF lang_eq_any :=
begin
  have concatenated : lang_eq_any = lang_aux_ab * lang_aux_c,
  {
    ext1 w,
    split,
    {
      rintro ⟨ n, m, hnm ⟩,
      fconstructor,
        use list.repeat a_ n ++ list.repeat b_ n,
        use list.repeat c_ m,
      split,
        use n,
      split,
        use m,
      exact hnm.symm,
    },
    {
      rintro ⟨ u, v, ⟨n, hu⟩, ⟨m, hv⟩, h ⟩,
      use n,
      use m,
      rw ← h,
      rw ← hu,
      rw ← hv,
    },
  },
  rw concatenated,
  apply CF_of_CF_c_CF,
  exact and.intro CF_lang_aux_ab CF_lang_aux_c,
end


private def lang_aux_a : language (fin 3) :=
λ w, ∃ n : ℕ, w = list.repeat a_ n

private lemma CF_lang_aux_a : is_CF lang_aux_a :=
sorry

private def lang_aux_bc : language (fin 3) :=
λ w, ∃ n : ℕ, w = list.repeat b_ n ++ list.repeat c_ n

private def permut : equiv.perm (fin 3) := equiv.mk
  (λ x, ite (x = 2) 0 (x + 1))
  (λ x, ite (x = 0) 2 (x - 1))
  (by {
    intro x,
    fin_cases x;
    refl,
  })
  (by {
    intro x,
    fin_cases x;
    refl,
  })

private lemma CF_lang_aux_bc : is_CF lang_aux_bc :=
begin
  have permuted : lang_aux_bc = permute_lang permut lang_aux_ab,
  {
    have compos : permut.to_fun ∘ permut.inv_fun = id,
    {
      simp,
    },
    ext1 w,
    split;
    {
      intro h,
      cases h with n hn,
      use n,
      try
      {
         rw hn
      },
      try
      {
        have other_case := congr_arg (list.map permut.to_fun) hn,
        rw list.map_map at other_case,
        rw compos at other_case,
        rw list.map_id at other_case,
        rw other_case,
      },
      rw list.map_append,
      rw list.map_repeat,
      rw list.map_repeat,
      apply congr_arg2;
      refl,
    },
  },
  rw permuted,
  exact CF_of_permute_CF permut lang_aux_ab CF_lang_aux_ab,
end

private lemma CF_lang_any_eq : is_CF lang_any_eq :=
begin
  have concatenated : lang_any_eq = lang_aux_a * lang_aux_bc,
  {
    ext1 w,
    split,
    {
      rintro ⟨ n, m, hnm ⟩,
      fconstructor,
        use list.repeat a_ n,
        use list.repeat b_ m ++ list.repeat c_ m,
      split,
        use n,
      split,
        use m,
      rw ← list.append_assoc,
      exact hnm.symm,
    },
    {
      rintro ⟨ u, v, ⟨n, hu⟩, ⟨m, hv⟩, h ⟩,
      use n,
      use m,
      rw ← h,
      rw list.append_assoc,
      rw ← hu,
      rw ← hv,
    },
  },
  rw concatenated,
  apply CF_of_CF_c_CF,
  exact and.intro CF_lang_aux_a CF_lang_aux_bc,
end

end yes_CF

end what_is_CF


section intersection_inclusions

private lemma intersection_of_lang_eq_eq {w : list (fin 3)} :
  w ∈ lang_eq_eq  →  w ∈ lang_eq_any ⊓ lang_any_eq :=
begin
  intro h,
  cases h with n hyp,
  split;
  {
    use n,
    use n,
    exact hyp,
  },
end

private lemma helper (n₁ m₁ n₂ m₂ : ℕ) (n₁pos : n₁ > 0)
                     (a_ b_ c_ : fin 3) (a_neq_b : a_ ≠ b_) (a_neq_c : a_ ≠ c_)
                     (equ: list.repeat a_ n₁ ++ list.repeat b_ n₁ ++ list.repeat c_ m₁ =
                           list.repeat a_ n₂ ++ list.repeat b_ m₂ ++ list.repeat c_ m₂) :
  n₁ ≤ n₂ :=
begin
  by_contradiction contr,
  have n₁_le_len₁ : (n₁ - 1) < (list.repeat a_ n₁ ++ (list.repeat b_ n₁ ++ list.repeat c_ m₁)).length,
  {
    rw ← list.append_assoc,
    rw list.length_append,
    rw list.length_append,
    rw list.length_repeat,
    rw add_assoc,
    apply nat.lt_add_right,
    exact nat.sub_lt n₁pos (nat.succ_pos 0),
  },
  have n₁_le_len₂ : (n₁ - 1) < (list.repeat a_ n₂ ++ (list.repeat b_ m₂ ++ list.repeat c_ m₂)).length,
  {
    rw ← list.append_assoc,
    have equ_len := congr_arg list.length equ,
    rw ← equ_len,
    rw list.append_assoc,
    exact n₁_le_len₁,
  },
  have n₁th : (list.repeat a_ n₁ ++ (list.repeat b_ n₁ ++ list.repeat c_ m₁)).nth_le (n₁ - 1) n₁_le_len₁ =
              (list.repeat a_ n₂ ++ (list.repeat b_ m₂ ++ list.repeat c_ m₂)).nth_le (n₁ - 1) n₁_le_len₂,
  {
    finish,
  },
  have n₁th₁ : (list.repeat a_ n₁ ++ (list.repeat b_ n₁ ++ list.repeat c_ m₁)).nth_le (n₁ - 1) n₁_le_len₁ = a_,
  {
    have foo : (n₁ - 1) < (list.repeat a_ n₁).length,
    {
      rw list.length_repeat,
      exact nat.sub_lt n₁pos (nat.succ_pos 0),
    },
    rw list.nth_le_append n₁_le_len₁ foo,
    exact list.nth_le_repeat a_ foo,
  },
  have n₁th₂ : (list.repeat a_ n₂ ++ (list.repeat b_ m₂ ++ list.repeat c_ m₂)).nth_le (n₁ - 1) n₁_le_len₂ ≠ a_,
  {
    have foo : (list.repeat a_ n₂).length ≤ (n₁ - 1),
    {
      rw list.length_repeat,
      push_neg at contr,
      exact nat.le_pred_of_lt contr,
    },
    rw list.nth_le_append_right foo n₁_le_len₂,
    by_contradiction,
    have a_in_bc : a_ ∈ (list.repeat b_ m₂ ++ list.repeat c_ m₂),
    {
      rw ← h,
      apply list.nth_le_mem,
    },
    rw list.mem_append at a_in_bc,
    cases a_in_bc,
    {
      rw list.mem_repeat at a_in_bc,
      exact a_neq_b a_in_bc.right,
    },
    {
      rw list.mem_repeat at a_in_bc,
      exact a_neq_c a_in_bc.right,
    }
  },
  rw n₁th₁ at n₁th,
  rw ← n₁th at n₁th₂,
  exact false_of_ne n₁th₂,
end

private lemma lang_eq_eq_of_intersection {w : list (fin 3)} :
  w ∈ lang_eq_any ⊓ lang_any_eq  →  w ∈ lang_eq_eq :=
begin
  rintro ⟨ ⟨ n₁, m₁, h₁ ⟩, ⟨ n₂, m₂, h₂ ⟩ ⟩,
  have equ := eq.trans h₁.symm h₂,

  by_cases hn₁ : n₁ = 0,
  {
    have hn₂ : n₂ = 0,
    {
      by_contradiction,
      have pos := nat.pos_of_ne_zero h,
      clear h,
      have a_in_equ := congr_arg (λ lis, a_ ∈ lis) equ,
      clear equ,
      rw hn₁ at a_in_equ,
      have a_yes : a_ ∈ list.repeat a_ n₂,
      {
        rw list.mem_repeat,
        exact and.intro (ne_of_lt pos).symm rfl,
      },
      simp [a_yes] at a_in_equ,
      rw list.mem_repeat at a_in_equ,
      have a_neq_c : a_ ≠ c_,
      {
        dec_trivial,
      },
      exact a_neq_c a_in_equ.right,
    },
    have hm₂ : m₂ = 0,
    {
      by_contradiction,
      have pos := nat.pos_of_ne_zero h,
      clear h,
      have b_in_equ := congr_arg (λ lis, b_ ∈ lis) equ,
      clear equ,
      rw hn₁ at b_in_equ,
      have b_yes : b_ ∈ list.repeat b_ m₂,
      {
        rw list.mem_repeat,
        exact and.intro (ne_of_lt pos).symm rfl,
      },
      simp [b_yes] at b_in_equ,
      rw list.mem_repeat at b_in_equ,
      have b_neq_c : b_ ≠ c_,
      {
        dec_trivial,
      },
      exact b_neq_c b_in_equ.right,
    },
    use 0,
    rw hn₂ at h₂,
    rw hm₂ at h₂,
    exact h₂,
  },

  have n₁pos : n₁ > 0 :=
    pos_iff_ne_zero.mpr hn₁,
  clear hn₁,

  have n₂pos : n₂ > 0,
    sorry, -- follows from `n₁pos` using `equ`
  have m₂pos : m₂ > 0,
  {
    by_contradiction,
    have m₂zero : m₂ = 0,
    {
      push_neg at h,
      rw nat.le_zero_iff at h,
      exact h,
    },
    clear h,
    rw m₂zero at equ,
    simp at equ,
    have b_in_equ := congr_arg (λ lis, b_ ∈ lis) equ,
    clear equ,
    simp at b_in_equ,
    have b_yes : b_ ∈ list.repeat b_ n₁,
    {
      rw list.mem_repeat,
      exact and.intro (ne_of_lt n₁pos).symm rfl,
    },
    have b_no : b_ ∉ list.repeat a_ n₂,
    {
      rw list.mem_repeat,
      by_contradiction,
      have b_ne_q : b_ ≠ a_,
      {
        dec_trivial,
      },
      exact b_ne_q h.right,
    },
    tauto,
  },
  have m₁pos : m₁ > 0,
    sorry, -- follows from `m₂pos` using `equ`

  have n_ge : n₁ ≥ n₂,
  {

    sorry,
  },
  have n_le : n₁ ≤ n₂,
  {
    exact helper n₁ m₁ n₂ m₂ n₁pos a_ b_ c_ (by dec_trivial) (by dec_trivial) equ,
  },
  have m_ge : m₁ ≥ m₂,
  {
    have rev := congr_arg list.reverse equ,
    clear equ,
    repeat { rw list.reverse_append at rev },
    repeat { rw list.reverse_repeat at rev },
    rw ← list.append_assoc at rev,
    rw ← list.append_assoc at rev,
    exact helper m₂ n₂ m₁ n₁ m₂pos c_ b_ a_ (by dec_trivial) (by dec_trivial) rev.symm,
  },
  have m_le : m₁ ≤ m₂,
  {
    have rev := congr_arg list.reverse equ,
    clear equ,
    repeat { rw list.reverse_append at rev },
    repeat { rw list.reverse_repeat at rev },
    rw ← list.append_assoc at rev,
    rw ← list.append_assoc at rev,

    sorry,
  },
  have eqn : n₁ = n₂ :=
    le_antisymm n_le n_ge,
  have eqm : m₁ = m₂ :=
    le_antisymm m_le m_ge,

  have sum_lens : n₁ + n₁ + m₁ = n₂ + m₂ + m₂,
  {
    have lens := congr_arg list.length equ,
    repeat { rw list.length_append at lens }, 
    repeat { rw list.length_repeat at lens }, 
    exact lens,
  },
  have eq₂ : n₂ = m₂,
  {
    rw eqn at sum_lens,
    rw eqm at sum_lens,
    rw add_left_inj at sum_lens,
    rw add_right_inj at sum_lens,
    exact sum_lens,
  },
  rw eq₂ at h₂,
  use m₂,
  exact h₂,    
end

end intersection_inclusions

end specific_defs_and_lemmata


/-- The class of context-free languages isn't closed under intersection. -/
theorem nnyCF_of_CF_i_CF : ¬ (∀ T : Type, ∀ L₁ : language T, ∀ L₂ : language T,
    is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ ⊓ L₂)
) :=
begin
  by_contradiction,
  specialize h (fin 3) lang_eq_any lang_any_eq,
  specialize h (and.intro CF_lang_eq_any CF_lang_any_eq),

  have intersection : lang_eq_any ⊓ lang_any_eq = lang_eq_eq,
  {
    apply set.eq_of_subset_of_subset,
    {
      apply lang_eq_eq_of_intersection,
    },
    {
      apply intersection_of_lang_eq_eq,
    },
  },
  
  rw intersection at h,
  exact notCF_lang_eq_eq h,
end
