import cfg
import cfgPumping
import tactic


section reusable_defs_and_lemmata

--def count_in {α : Type} [h : decidable (λ x y : α, x = y)] (lis : list α) (a : α) : ℕ :=
def count_in (w : list (fin 3)) (a : (fin 3)) : ℕ :=
list.sum (list.map (λ x, ite (x = a) 1 0) w)

lemma count_in_repeat_eq (a : (fin 3)) (n : ℕ) :
  count_in (list.repeat a n) a  =  n  :=
begin
  sorry,
end

lemma count_in_repeat_neq {a : (fin 3)} {b : (fin 3)} (h : a ≠ b) (n : ℕ) :
  count_in (list.repeat a n) b  =  0  :=
begin
  sorry,
end

lemma count_in_append (w₁ w₂ : list (fin 3)) (a : (fin 3)) :
  count_in (w₁ ++ w₂) a  =  count_in w₁ a  +  count_in w₂ a  :=
begin
  rw count_in,
  rw list.map_append,
  rw list.sum_append,
  refl,
end

lemma count_in_le_length {w : list (fin 3)} {a : (fin 3)} :
  count_in w a ≤ w.length :=
begin
  rw count_in,
  have upper_bound : ∀ y : (fin 3), (λ (x : fin 3), ite (x = a) 1 0) y ≤ 1,
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
  calc (list.map (λ (x : fin 3), ite (x = a) 1 0) w).sum
      ≤ (list.map (λ (x : fin 3), 1) w).sum : sorry
  ... ≤ 1 * w.length                        : sorry
  ... = w.length                            : by rw one_mul,
end

lemma count_in_pos_of_in {w : list (fin 3)} {a : (fin 3)} (h : a ∈ w) :
  count_in w a > 0 :=
begin
  by_contradiction contr,
  rw not_lt at contr,
  rw nat.le_zero_iff at contr,
  sorry,
end

lemma count_in_zero_of_notin {w : list (fin 3)} {a : (fin 3)} (h : a ∉ w) :
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
  rcases pump with ⟨ u, v, x, y, z, concatenating, nonempty, short, pumping ⟩,
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
    have long : (v ++ x ++ y).length > n,
    {
      by_contradiction contr,
      push_neg at contr,
      have bees : count_in (v ++ x ++ y) b_ ≤ n,
      {
        calc count_in (v ++ x ++ y) b_
            ≤ (v ++ x ++ y).length : count_in_le_length
        ... ≤ n                    : contr,
      },
      -- we have `concatenating: list.repeat a_ (n + 1) ++ list.repeat b_ (n + 1) ++ list.repeat c_ (n + 1) = u ++ v ++ x ++ y ++ z`
      -- for the middle part `v ++ x ++ y` to contain both `a_` and `c_`
      -- it would have to contain the whole segment `list.repeat b_ (n + 1)` also
      -- which is in contradiction with `(v ++ x ++ y).length ≤ n` qed
      sorry,
    },
    exact not_le_of_gt long short,
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
