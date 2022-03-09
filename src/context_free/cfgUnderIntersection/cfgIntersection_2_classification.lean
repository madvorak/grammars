import context_free.cfgUnderIntersection.cfgIntersection_1_basic


lemma CF_lang_eq_any : is_CF lang_eq_any :=
sorry

lemma CF_lang_any_eq : is_CF lang_any_eq :=
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

lemma notCF_lang_eq_eq : ¬ is_CF lang_eq_eq :=
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
