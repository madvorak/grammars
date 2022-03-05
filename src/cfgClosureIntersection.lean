import cfg
import cfgPumping
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
-- maybe not needed in the end
begin
  rw count_in,
  have upper_bound : ∀ y : (α), (λ (x : α), ite (x = a) 1 0) y ≤ 1,
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

private def lang_eq_any : language (fin 3) :=
λ w, ∃ n m : ℕ, w = list.repeat a_ n ++ list.repeat b_ n ++ list.repeat c_ m

private def lang_any_eq : language (fin 3) :=
λ w, ∃ n m : ℕ, w = list.repeat a_ n ++ list.repeat b_ m ++ list.repeat c_ m

private def lang_eq_eq : language (fin 3) :=
λ w, ∃ n : ℕ, w = list.repeat a_ n ++ list.repeat b_ n ++ list.repeat c_ n

private lemma CF_lang_eq_any : is_CF lang_eq_any :=
sorry

private lemma CF_lang_any_eq : is_CF lang_any_eq :=
sorry

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

private lemma lang_eq_eq_of_intersection {w : list (fin 3)} :
  w ∈ lang_eq_any ⊓ lang_any_eq  →  w ∈ lang_eq_eq :=
begin
  rintro ⟨ ⟨ n₁, m₁, h₁ ⟩, ⟨ n₂, m₂, h₂ ⟩ ⟩,
  have equ := eq.trans h₁.symm h₂,

  have n_ge : n₁ ≥ n₂,
  {
    
    sorry,
  },
  have n_le : n₁ ≤ n₂,
  {
    by_contradiction contr,
    -- probably messed up
    have n₂th := congr_arg (λ li, list.nth li (n₂ - 1)) equ,
    simp at n₂th,
    have n₂th₁ : (list.repeat a_ n₁ ++ (list.repeat b_ n₁ ++ list.repeat c_ m₁)).nth (n₂ - 1) = some a_,
    {
      have n₂pos : n₂ > 0,
        sorry, -- TODO at the beginning of the proof !!!
      have foo : n₂ - 1 < (list.repeat a_ n₂).length,
      {
        apply nat.lt_of_succ_le,
        apply le_of_eq,
        rw list.length_repeat,
        exact nat.succ_pred_eq_of_pos n₂pos,
      },
      rw list.nth_append foo at n₂th,
      convert n₂th,
      rw list.nth_le_nth foo,
      rw list.nth_le_repeat,
    },
    have n₂th₂ : (list.take n₂ (list.repeat a_ n₂ ++ (list.repeat b_ m₂ ++ list.repeat c_ m₂))).nth (n₂ - 1) ≠ some a_,
    {

      sorry,
    },
    
    sorry,
  },
  have m_ge : m₁ ≥ m₂,
  {

    sorry,
  },
  have m_le : m₁ ≤ m₂,
  {

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
