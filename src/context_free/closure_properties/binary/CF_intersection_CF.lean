import context_free.cfgPumping
import context_free.cfgElementary
import context_free.closure_properties.binary.CF_concatenation_CF
import context_free.closure_properties.unary.permutation_CF


section reusable_defs_and_lemmata
variables {α : Type} [decidable_eq α]

def count_in (w : list α) (a : α) : ℕ :=
list.sum (list.map (λ x, ite (x = a) 1 0) w)

lemma count_in_repeat_eq (a : α) (n : ℕ) :
  count_in (list.repeat a n) a  =  n  :=
begin
  induction n with n ih,
  {
    refl,
  },
  change count_in (a :: list.repeat a n) a = n.succ,
  unfold count_in,
  unfold list.map,
  simp,
  exact nat.one_add n,
end

lemma count_in_repeat_neq {a : α} {b : α} (hyp : a ≠ b) (n : ℕ) :
  count_in (list.repeat a n) b  =  0  :=
begin
  induction n with n ih,
  {
    refl,
  },
  change count_in (a :: list.repeat a n) b = 0,
  unfold count_in,
  unfold list.map,
  simp,
  split,
  {
    exact hyp,
  },
  intro h,
  exfalso,
  exact hyp h,
end

lemma count_in_append (w₁ w₂ : list α) (a : α) :
  count_in (w₁ ++ w₂) a  =  count_in w₁ a  +  count_in w₂ a  :=
begin
  rw count_in,
  rw list.map_append,
  rw list.sum_append,
  refl,
end

lemma count_in_pos_of_in {w : list α} {a : α} (hyp : a ∈ w) :
  count_in w a > 0 :=
begin
  induction w with head tail ih,
  {
    exfalso,
    rw list.mem_nil_iff at hyp,
    exact hyp,
  },
  by_contradiction contr,
  rw not_lt at contr,
  rw nat.le_zero_iff at contr,
  rw list.mem_cons_eq at hyp,
  unfold count_in at contr,
  unfold list.map at contr,
  simp at contr,
  cases hyp,
  {
    exact contr.left hyp.symm,
  },
  specialize ih hyp,
  have zero_in_tail : count_in tail a = 0,
  {
    unfold count_in,
    exact contr.right,
  },
  rw zero_in_tail at ih,
  exact nat.lt_asymm ih ih,
end

lemma count_in_zero_of_notin {w : list α} {a : α} (hyp : a ∉ w) :
  count_in w a = 0 :=
begin
  induction w with head tail ih,
  {
    refl,
  },
  unfold count_in,
  rw list.map_cons,
  simp,
  rw list.mem_cons_eq at hyp,
  push_neg at hyp,
  split,
  {
    exact hyp.left.symm,
  },
  exact ih hyp.right,
end

end reusable_defs_and_lemmata


section specific_defs_and_lemmata

private def a_ : fin 3 := 0
private def b_ : fin 3 := 1
private def c_ : fin 3 := 2

private def a : symbol (fin 3) (fin 1) := symbol.terminal a_
private def b : symbol (fin 3) (fin 1) := symbol.terminal b_
private def c : symbol (fin 3) (fin 1) := symbol.terminal c_

private lemma neq_ab : a_ ≠ b_ := by dec_trivial
private lemma neq_ba : b_ ≠ a_ := neq_ab.symm
private lemma neq_ac : a_ ≠ c_ := by dec_trivial
private lemma neq_ca : c_ ≠ a_ := neq_ac.symm
private lemma neq_bc : b_ ≠ c_ := by dec_trivial
private lemma neq_cb : c_ ≠ b_ := neq_bc.symm


private def lang_eq_any : language (fin 3) :=
λ w, ∃ n m : ℕ, w = list.repeat a_ n ++ list.repeat b_ n ++ list.repeat c_ m

private def lang_any_eq : language (fin 3) :=
λ w, ∃ n m : ℕ, w = list.repeat a_ n ++ list.repeat b_ m ++ list.repeat c_ m

private def lang_eq_eq : language (fin 3) :=
λ w, ∃ n : ℕ, w = list.repeat a_ n ++ list.repeat b_ n ++ list.repeat c_ n


section what_is_CF

section not_CF

private lemma false_of_uvvxyyz
    {_a _b _c : fin 3} {n : ℕ} {u v x y z : list (fin 3)}
    (elimin : ∀ s : fin 3,  s ≠ _a  →  s ≠ _b  →  s ≠ _c  → false)
    (no_a : _a ∉ v ++ y) (nonempty : (v ++ y).length > 0)
    (counts_ab : ∀ (w : list (fin 3)), w ∈ lang_eq_eq → count_in w _a = count_in w _b)
    (counts_ac : ∀ (w : list (fin 3)), w ∈ lang_eq_eq → count_in w _a = count_in w _c)
    (counted_a : count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _a = n + 1 + count_in (v ++ y) _a)
    (counted_b : count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _b = n + 1 + count_in (v ++ y) _b)
    (counted_c : count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) _c = n + 1 + count_in (v ++ y) _c)
    (pumping : u ++ v ^ 2 ++ x ++ y ^ 2 ++ z ∈ lang_eq_eq) :
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
      exact elimin ((v ++ y).nth_le 0 nonempty) first_letter_not_a first_letter_not_b first_letter_not_c,
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
  rcases pump with ⟨u, v, x, y, z, concatenating, nonempty, vxy_short, pumping⟩,
  specialize pumping 2,

  have not_all_letters : a_ ∉ (v ++ y) ∨ b_ ∉ (v ++ y) ∨ c_ ∉ (v ++ y),
  {
    by_contradiction contr,
    push_neg at contr,
    rcases contr with ⟨hva, -, hvc⟩,

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
        rw ← list.length_append_append at total_length,
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
        rcases list.nth_le_of_mem relaxed_a with ⟨nₐ, hnₐ, h_nthₐ⟩,
        obtain ⟨h_nth_a_pr, h_nth_a⟩ : ∃ proofoo, (v ++ x ++ y ++ z).nth_le ((nₐ + u.length) - u.length) proofoo = a_,
        {
          rw nat.add_sub_cancel nₐ u.length,
          use hnₐ,
          exact h_nthₐ,
        },
        have lt_len : (nₐ + u.length) < (u ++ (v ++ x ++ y ++ z)).length,
        {
          rw list.length_append,
          linarith,
        },
        rw ← list.nth_le_append_right le_add_self lt_len at h_nth_a,

        have orig_nth_le_eq_a :
          ∃ proofoo,
            (list.repeat a_ (n + 1) ++ (list.repeat b_ (n + 1) ++ list.repeat c_ (n + 1))).nth_le
              (nₐ + u.length) proofoo =
            a_,
        {
          have rebracket : u ++ (v ++ (x ++ (y ++ z))) = u ++ (v ++ x ++ y ++ z),
          {
            simp only [list.append_assoc],
          },
          rw concatenating,
          rw rebracket,
          use lt_len,
          exact h_nth_a,
        },
        cases orig_nth_le_eq_a with rrr_nth_le_eq_a_pr rrr_nth_le_eq_a,

        rw @list.nth_le_append_right (fin 3)
          (list.repeat a_ (n + 1))
          (list.repeat b_ (n + 1) ++ list.repeat c_ (n + 1))
          (nₐ + u.length)
          (by {
            rw list.length_repeat,
            calc n + 1 ≤ u.length      : u_too_much
                 ...   ≤ nₐ + u.length : le_add_self,
          })
          (by {
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
          rcases list.nth_le_of_mem relaxed_c with ⟨m, hm, mth_is_c⟩,

          have m_big : m ≥ 2 * n + 2,
          {
            have orig_mth_is_c :
              ∃ proofoo,
                ((list.repeat a_ (n + 1) ++ list.repeat b_ (n + 1)) ++ list.repeat c_ (n + 1)).nth_le
                  m proofoo =
                c_,
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

  have counted_letter : ∀ s,
    count_in (u ++ v ++ x ++ y ++ z ++ (v ++ y)) s =
    count_in (list.repeat a_ (n+1)) s + count_in (list.repeat b_ (n+1)) s +
      count_in (list.repeat c_ (n+1)) s + count_in (v ++ y) s,
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
begin
  let S_ : fin 1 := 0,
  let S : symbol (fin 3) (fin 1) := symbol.nonterminal S_,
  let g := CF_grammar.mk
    (fin 1)
    S_
    [
      (S_, [a, S, b]),
      (S_, ([] : list (symbol (fin 3) (fin 1))))
    ],
  use g,
  apply set.eq_of_subset_of_subset,
  {
    intros w ass,
    change CF_derives g [S] (list.map symbol.terminal w) at ass,
    have indu :
      ∀ v : list (symbol (fin 3) (fin 1)),
        CF_derives g [S] v →
          ∃ n : ℕ,
            v = list.repeat a n ++ list.repeat b n   ∨
            v = list.repeat a n ++ [S] ++ list.repeat b n,
    {
      intros v hyp,
      induction hyp with u u' trash orig hyp_ih,
      {
        use 0,
        right,
        refl,
      },
      rcases orig with ⟨rul, rin, p, q, bef, aft⟩,
      cases hyp_ih with k ih,
      cases ih,
      {
        exfalso,
        rw ih at bef,
        have yes_in : symbol.nonterminal rul.fst ∈ p ++ [symbol.nonterminal rul.fst] ++ q,
        {
          apply list.mem_append_left,
          apply list.mem_append_right,
          apply list.mem_cons_self,
        },
        have not_in : symbol.nonterminal rul.fst ∉ list.repeat a k ++ list.repeat b k,
        {
          rw list.mem_append_eq,
          push_neg,
          split;
          {
            rw list.mem_repeat,
            push_neg,
            intro trash,
            tauto,
          },
        },
        rw bef at not_in,
        exact not_in yes_in,
      },
      
      have both_rule_rewrite_S : symbol.nonterminal rul.fst = S,
      {
        cases rin,
        {
          rw rin,
        },
        cases rin,
        {
          rw rin,
        },
        cases rin,
      },
      rw bef at ih,
      rw both_rule_rewrite_S at ih,
      dsimp at ih,
      have p_len : p.length = k,
      {
        by_contradiction contra,
        have kth_eq := congr_fun (congr_arg list.nth ih) p.length,
        have plengthth_is_S : (p ++ [S] ++ q).nth p.length = some S,
        {
          rw list.append_assoc,
          rw list.nth_append_right (le_of_eq rfl),
          {
            rw nat.sub_self,
            refl,
          },
        },
        rw plengthth_is_S at kth_eq,

        cases lt_or_gt_of_ne contra,
        {
          have plengthth_is_a :
            (list.repeat a k ++ [S] ++ list.repeat b k).nth p.length =
            some a,
          {
            rw list.append_assoc,
            have plength_small : p.length < (list.repeat a k).length,
            {
              rw list.length_repeat,
              exact h,
            },
            rw list.nth_append plength_small,
            rw list.nth_le_nth plength_small,
            apply congr_arg,
            exact list.nth_le_repeat a plength_small,
          },
          rw plengthth_is_a at kth_eq,
          have S_neq_a : S ≠ a,
          {
            tauto,
          },
          rw option.some_inj at kth_eq,
          exact S_neq_a kth_eq,
        },
        {
          have plengthth_is_b :
            (list.repeat a k ++ [S] ++ list.repeat b k).nth p.length =
            some b,
          {
            have plength_big : (list.repeat a k ++ [S]).length ≤ p.length,
            {
              rw list.length_append,
              rw list.length_repeat,
              exact nat.succ_le_iff.mpr h,
            },
            rw list.nth_append_right plength_big,
            have len_within_list : p.length - (list.repeat a k ++ [S]).length < (list.repeat b k).length,
            {
              have ihlen := congr_arg list.length ih,
              simp only [list.length_repeat, list.length_append, list.length_singleton] at *,
              have ihlen' : p.length + 1 ≤ k + 1 + k,
              {
                exact nat.le.intro ihlen,
              },
              have ihlen'' : p.length < k + 1 + k,
              {
                exact nat.succ_le_iff.mp ihlen',
              },
              rw ← tsub_lt_iff_left plength_big at ihlen'',
              exact ihlen'',
            },
            rw list.nth_le_nth len_within_list,
            apply congr_arg,
            exact list.nth_le_repeat b len_within_list,
          },
          rw plengthth_is_b at kth_eq,
          have S_neq_b : S ≠ b,
          {
            tauto,
          },
          rw option.some_inj at kth_eq,
          exact S_neq_b kth_eq,
        },
      },
      have ihl_len : (p ++ [symbol.nonterminal S_]).length = k + 1,
      {
        rw list.length_append,
        rw p_len,
        refl,
      },
      have ihr_len : (list.repeat a k ++ [S]).length = k + 1,
      {
        rw list.length_append,
        rw list.length_repeat,
        refl,
      },
      have qb : q = list.repeat b k,
      {
        apply list.append_inj_right ih,
        rw ihl_len,
        rw ihr_len,
      },
      have ih_reduced : p ++ [symbol.nonterminal S_] = list.repeat a k ++ [S],
      {
        rw qb at ih,
        rw list.append_left_inj at ih,
        exact ih,
      },
      have pa : p = list.repeat a k,
      {
        rw list.append_left_inj at ih_reduced,
        exact ih_reduced,
      },

      cases rin,
      {
        use k + 1,
        right,
        rw aft,
        rw rin,
        convert_to
          p ++ (S_, [a, S, b]).snd ++ q =
          list.repeat a k ++ [a] ++ [S] ++ [b] ++ list.repeat b k,
        {
          rw list.repeat_add,
          rw add_comm,
          rw list.repeat_add,
          simp only [list.repeat, list.append_assoc],
        },
        rw [pa, qb],
        simp only [list.append_assoc, list.cons_append, list.singleton_append],
      },
      cases rin,
      {
        use k,
        left,
        rw aft,
        rw rin,
        rw list.append_nil,
        rw [pa, qb],
      },
      exfalso,
      exact rin,
    },
    cases indu (list.map symbol.terminal w) ass with n instantiated,
    clear indu,
    cases instantiated,
    {
      use n,
      have foo := congr_arg (list.filter_map (
        λ z : symbol (fin 3) (fin 1),
          match z with
            | symbol.terminal t := some t
            | symbol.nonterminal _ := none
          end
        )) instantiated,
      rw list.filter_map_append at foo,
      rw list.filter_map_map at foo,
      rw list.filter_map_some at foo,
      rw [foo, a, b],
      clear foo,
      apply congr_arg2;
      {
        clear instantiated,
        induction n with n ih,
        {
          refl,
        },
        rw list.repeat_succ,
        rw list.repeat_succ,
        rw list.filter_map_cons,
        simp only [eq_self_iff_true, true_and, ih],
      },
    },
    exfalso,
    have yes_in : S ∈ list.repeat a n ++ [S] ++ list.repeat b n,
    {
      apply list.mem_append_left,
      apply list.mem_append_right,
      apply list.mem_cons_self,
    },
    have not_in : S ∉ list.map symbol.terminal w,
    {
      intro hyp,
      have S_isnt_terminal : ¬ ∃ x, S = symbol.terminal x,
      {
        tauto,
      },
      rw list.mem_map at hyp,
      cases hyp with y hypo,
      push_neg at S_isnt_terminal,
      exact S_isnt_terminal y hypo.right.symm,
    },
    rw instantiated at not_in,
    exact not_in yes_in,
  },
  {
    intros w ass,
    cases ass with n hw,
    change CF_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w),
    rw [hw, list.map_append, list.map_repeat, list.map_repeat, ← a, ← b],
    clear hw,
    induction n with n ih,
    {
      convert_to CF_derives g [symbol.nonterminal g.initial] [],
      apply CF_deri_of_tran,
      use (S_, ([] : list (symbol (fin 3) (fin 1)))),
      split,
      {
        apply list.mem_cons_of_mem,
        apply list.mem_cons_self,
      },
      use [[], []],
      split;
      refl,
    },
    convert_to
      CF_derives g
        [symbol.nonterminal g.initial]
        (list.map
          symbol.terminal
          ([a_] ++ (list.repeat a_ n ++ list.repeat b_ n) ++ [b_])
        ),
    {
      convert_to
        list.repeat a (1 + n) ++ list.repeat b (n + 1) =
        list.map symbol.terminal ([a_] ++ (list.repeat a_ n ++ list.repeat b_ n) ++ [b_]),
      {
        rw add_comm,
      },
      rw [
        list.map_append_append,
        list.map_singleton,
        list.map_singleton,
        list.repeat_add,
        list.repeat_add,
        a, b
      ],
      simp only [list.repeat, list.append_assoc, list.map_append, list.map_repeat],
    },
    apply CF_deri_of_tran_deri,
    {
      use (S_, [a, S, b]),
      split,
      {
        apply list.mem_cons_self,
      },
      use [[], []],
      split;
      refl,
    },
    rw list.map_append_append,
    change
      CF_derives g
        ([a] ++ [S] ++ [b])
        ([a] ++ list.map symbol.terminal (list.repeat a_ n ++ list.repeat b_ n) ++ [b]),
    apply CF_derives_with_prefix_and_postfix,
    convert ih,
    rw [list.map_append, list.map_repeat, list.map_repeat, a, b],
  },
end

private def lang_aux_c : language (fin 3) :=
λ w, ∃ n : ℕ, w = list.repeat c_ n

private lemma CF_lang_aux_c : is_CF lang_aux_c :=
begin
  use cfg_symbol_star c_,
  unfold lang_aux_c,
  apply language_of_cfg_symbol_star,
end

private lemma CF_lang_eq_any : is_CF lang_eq_any :=
begin
  have concatenated : lang_eq_any = lang_aux_ab * lang_aux_c,
  {
    ext1 w,
    split,
    {
      rintro ⟨n, m, hnm⟩,
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
      rintro ⟨u, v, ⟨n, hu⟩, ⟨m, hv⟩, h⟩,
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
begin
  use cfg_symbol_star a_,
  unfold lang_aux_a,
  apply language_of_cfg_symbol_star,
end

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
  have permuted : lang_aux_bc = permute_lang lang_aux_ab permut,
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
      rintro ⟨n, m, hnm⟩,
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
      rintro ⟨u, v, ⟨n, hu⟩, ⟨m, hv⟩, h⟩,
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

private lemma doubled_le_singled
    (n₁ m₁ n₂ m₂ : ℕ) (n₁pos : n₁ > 0)
    (a_ b_ c_ : fin 3) (a_neq_b : a_ ≠ b_) (a_neq_c : a_ ≠ c_)
    (equ :
      list.repeat a_ n₁ ++ list.repeat b_ n₁ ++ list.repeat c_ m₁ =
      list.repeat a_ n₂ ++ list.repeat b_ m₂ ++ list.repeat c_ m₂
    ) :
  n₁ ≤ n₂ :=
begin
  by_contradiction contr,
  push_neg at contr,

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
  have n₁th :
    (list.repeat a_ n₁ ++ (list.repeat b_ n₁ ++ list.repeat c_ m₁)).nth_le (n₁ - 1) n₁_le_len₁ =
    (list.repeat a_ n₂ ++ (list.repeat b_ m₂ ++ list.repeat c_ m₂)).nth_le (n₁ - 1) n₁_le_len₂,
  {
    rw list.append_assoc at equ,
    rw list.append_assoc at equ,
    exact list.nth_le_of_eq equ n₁_le_len₁,
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
    },
  },
  rw n₁th₁ at n₁th,
  rw ← n₁th at n₁th₂,
  exact false_of_ne n₁th₂,
end

private lemma doubled_ge_singled
    (n₁ m₁ n₂ m₂ : ℕ) (n₂pos : n₂ > 0)
    (a_ b_ c_ : fin 3) (a_neq_b : a_ ≠ b_) (a_neq_c : a_ ≠ c_)
    (equ :
      list.repeat a_ n₁ ++ list.repeat b_ n₁ ++ list.repeat c_ m₁ =
      list.repeat a_ n₂ ++ list.repeat b_ m₂ ++ list.repeat c_ m₂
    ) :
  n₁ ≥ n₂ :=
begin
  by_contradiction contr,
  push_neg at contr,

  have n₂_le_len₂ : (n₂ - 1) < (list.repeat a_ n₂ ++ (list.repeat b_ m₂ ++ list.repeat c_ m₂)).length,
  {
    rw ← list.append_assoc,
    rw list.length_append,
    rw list.length_append,
    rw list.length_repeat,
    rw add_assoc,
    apply nat.lt_add_right,
    exact nat.sub_lt n₂pos (nat.succ_pos 0),
  },
  have n₂_le_len₁ : (n₂ - 1) < (list.repeat a_ n₁ ++ (list.repeat b_ n₁ ++ list.repeat c_ m₁)).length,
  {
    rw ← list.append_assoc,
    have equ_len := congr_arg list.length equ,
    rw equ_len,
    rw list.append_assoc,
    exact n₂_le_len₂,
  },
  have n₂th :
    (list.repeat a_ n₁ ++ (list.repeat b_ n₁ ++ list.repeat c_ m₁)).nth_le (n₂ - 1) n₂_le_len₁ =
    (list.repeat a_ n₂ ++ (list.repeat b_ m₂ ++ list.repeat c_ m₂)).nth_le (n₂ - 1) n₂_le_len₂,
  {
    rw list.append_assoc at equ,
    rw list.append_assoc at equ,
    exact list.nth_le_of_eq equ n₂_le_len₁,
  },
  have n₂th₂ : (list.repeat a_ n₂ ++ (list.repeat b_ m₂ ++ list.repeat c_ m₂)).nth_le (n₂ - 1) n₂_le_len₂ = a_,
  {
    have foo : (n₂ - 1) < (list.repeat a_ n₂).length,
    {
      rw list.length_repeat,
      exact nat.sub_lt n₂pos (nat.succ_pos 0),
    },
    rw list.nth_le_append n₂_le_len₂ foo,
    exact list.nth_le_repeat a_ foo,
  },
  have n₂th₁ : (list.repeat a_ n₁ ++ (list.repeat b_ n₁ ++ list.repeat c_ m₁)).nth_le (n₂ - 1) n₂_le_len₁ ≠ a_,
  {
    have foo : (list.repeat a_ n₁).length ≤ (n₂ - 1),
    {
      rw list.length_repeat,
      exact nat.le_pred_of_lt contr,
    },
    rw list.nth_le_append_right foo n₂_le_len₁,
    by_contradiction,
    have a_in_bc : a_ ∈ (list.repeat b_ n₁ ++ list.repeat c_ m₁),
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
    },
  },
  rw n₂th₂ at n₂th,
  rw n₂th at n₂th₁,
  exact false_of_ne n₂th₁,
end

private lemma lang_eq_eq_of_intersection {w : list (fin 3)} :
  w ∈ lang_eq_any ⊓ lang_any_eq  →  w ∈ lang_eq_eq :=
begin
  rintro ⟨⟨n₁, m₁, h₁⟩, ⟨n₂, m₂, h₂⟩⟩,
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
      exact neq_ac a_in_equ.right,
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
      exact neq_bc b_in_equ.right,
    },
    use 0,
    rw hn₂ at h₂,
    rw hm₂ at h₂,
    exact h₂,
  },
  have n₁pos : n₁ > 0 := pos_iff_ne_zero.mpr hn₁,

  have n₂pos : n₂ > 0,
  {
    by_contradiction,
    have n₂zero : n₂ = 0,
    {
      push_neg at h,
      rw nat.le_zero_iff at h,
      exact h,
    },
    clear h,
    rw n₂zero at equ,
    simp at equ,
    have a_in_equ := congr_arg (λ lis, a_ ∈ lis) equ,
    clear equ,
    simp at a_in_equ,
    repeat { rw list.mem_repeat at a_in_equ },
    have rs_false : (m₂ ≠ 0 ∧ a_ = b_ ∨ m₂ ≠ 0 ∧ a_ = c_) = false,
    {
      apply eq_false_intro,
      push_neg,
      split,
      {
        intro trash,
        exact neq_ab,
      },
      {
        intro trash,
        exact neq_ac,
      },
    },
    rw ← rs_false,
    rw ← a_in_equ,
    left,
    split,
    {
      exact hn₁,
    },
    {
      refl,
    },
  },
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
      exact neq_ba h.right,
    },
    tauto,
  },
  have m₁pos : m₁ > 0,
  {
    by_contradiction,
    have m₁zero : m₁ = 0,
    {
      push_neg at h,
      rw nat.le_zero_iff at h,
      exact h,
    },
    clear h,
    rw m₁zero at equ,
    simp at equ,
    have c_in_equ := congr_arg (λ lis, c_ ∈ lis) equ,
    clear equ,
    simp at c_in_equ,
    repeat { rw list.mem_repeat at c_in_equ },
    have ls_false : (n₁ ≠ 0 ∧ c_ = a_ ∨ n₁ ≠ 0 ∧ c_ = b_) = false,
    {
      apply eq_false_intro,
      push_neg,
      split,
      {
        intro trash,
        exact neq_ca,
      },
      {
        intro trash,
        exact neq_cb,
      },
    },
    rw ls_false at c_in_equ,
    rw c_in_equ,
    right,
    right,
    split,
    {
      exact ne_of_gt m₂pos,
    },
    {
      refl,
    },
  },

  have n_ge : n₁ ≥ n₂,
  {
    exact doubled_ge_singled n₁ m₁ n₂ m₂ n₂pos a_ b_ c_ neq_ab neq_ac equ,
  },
  have n_le : n₁ ≤ n₂,
  {
    exact doubled_le_singled n₁ m₁ n₂ m₂ n₁pos a_ b_ c_ neq_ab neq_ac equ,
  },
  have m_ge : m₁ ≥ m₂,
  {
    have rev := congr_arg list.reverse equ,
    clear equ,
    repeat { rw list.reverse_append at rev },
    repeat { rw list.reverse_repeat at rev },
    rw ← list.append_assoc at rev,
    rw ← list.append_assoc at rev,
    exact doubled_le_singled m₂ n₂ m₁ n₁ m₂pos c_ b_ a_ neq_cb neq_ca rev.symm,
  },
  have m_le : m₁ ≤ m₂,
  {
    have rev := congr_arg list.reverse equ,
    clear equ,
    repeat { rw list.reverse_append at rev },
    repeat { rw list.reverse_repeat at rev },
    rw ← list.append_assoc at rev,
    rw ← list.append_assoc at rev,
    exact doubled_ge_singled m₂ n₂ m₁ n₁ m₁pos c_ b_ a_ neq_cb neq_ca rev.symm,
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
