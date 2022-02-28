import cfg
import cfgPumping
import tactic


--def count_in {α : Type} [h : decidable (λ x y : α, x = y)] (lis : list α) (a : α) : ℕ :=
def count_in (lis : list (fin 3)) (a : (fin 3)) : ℕ :=
list.sum (list.map (λ x, ite (x = a) 1 0) lis)

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

lemma count_in_append (l₁ l₂ : list (fin 3)) (a : (fin 3)) :
  count_in (l₁ ++ l₂) a  =  count_in l₁ a  +  count_in l₂ a  :=
begin
  sorry,
end


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

private lemma notCF_lang_eq_eq : ¬ is_CF lang_eq_eq :=
begin
  intro h,
  have pum := CF_pumping h,
  cases pum with n pumm,
  specialize pumm (list.repeat a_ n ++ list.repeat b_ n ++ list.repeat c_ n),
  specialize pumm (by { use n, }) (by {
    rw list.length_append,
    rw list.length_repeat,
    apply le_add_self,
  }),
  cases pumm with u foo,
  cases foo with v bar,
  cases bar with x baz,
  cases baz with y qux,
  cases qux with z quux,
  cases quux with concatenating quuux,
  cases quuux with nonempty quuuux,
  cases quuuux with short pumping,
  specialize pumping 2,

  have neq_ab : a_ ≠ b_,
  {
    rw a_,
    rw b_,
    finish,
  },
  have neq_ac : a_ ≠ c_,
  {
    sorry,
  },
  have neq_bc : b_ ≠ c_,
  {
    sorry,
  },
  have neq_ba := neq_ab.symm,
  have neq_ca := neq_ac.symm,
  have neq_cb := neq_bc.symm,

  have not_all_letters : a_ ∉ (v ++ y) ∨ b_ ∉ (v ++ y) ∨ c_ ∉ (v ++ y),
  {
    
    sorry,
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
  cases not_all_letters with no_a rest,
  {
    have extra_not_a : b_ ∈ (v ++ y) ∨ c_ ∈ (v ++ y),
    {

      sorry,
    },
    have hab := counts_ab (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) pumping,
    have hac := counts_ac (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) pumping,

    cases pumping with n' pump',
    have count_a : count_in (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) a_ = n,
    {
      unfold list_n_times,
      simp [- list.append_assoc],
      repeat { rw count_in_append },
      have rearrange :
        count_in u a_ + (count_in v a_ + count_in v a_) + count_in x a_ + (count_in y a_ + count_in y a_) + count_in z a_ =
        (count_in u a_ + count_in v a_ + count_in x a_ + count_in y a_ + count_in z a_) + (count_in v a_ + count_in y a_),
      {
        ring,
      },
      have zero_in_v : count_in v a_ = 0,
      {
        --follows from `no_a`
        rw list.mem_append at no_a,
        sorry,
      },
      have zero_in_y : count_in y a_ = 0,
      {
        --follows from `no_a`
        rw list.mem_append at no_a,
        sorry,
      },
      rw rearrange,
      repeat { rw ← count_in_append },
      rw ← concatenating,
      repeat { rw count_in_append },
      rw zero_in_v,
      rw zero_in_y,
      rw count_in_repeat_eq a_,
      rw count_in_repeat_neq neq_ba,
      rw count_in_repeat_neq neq_ca,
      repeat { rw add_zero },
    },
    
    cases extra_not_a with extra_b extrac,
    {
      have count_b : count_in (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) b_ > n,
      {
        unfold list_n_times,
        simp [- list.append_assoc],
        repeat { rw count_in_append },
        have big_equality :
          count_in u b_ + (count_in v b_ + count_in v b_) + count_in x b_ + (count_in y b_ + count_in y b_) + count_in z b_ =
          (count_in u b_ + count_in v b_ + count_in x b_ + count_in y b_ + count_in z b_) + (count_in v b_ + count_in y b_),
        {
          ring,
        },
        rw big_equality,
        repeat { rw ← count_in_append },
        rw ← concatenating,
        repeat { rw count_in_append },
        rw count_in_repeat_eq b_,
        rw count_in_repeat_neq neq_ab,
        rw count_in_repeat_neq neq_cb,
        rw ← count_in_append,
        have at_least_one_b : count_in (v ++ y) b_ > 0,
        {
          --follows from `extra_b`
          sorry,
        },
        linarith,
      },
      rw count_a at hab,
      rw hab at count_b,
      exact has_lt.lt.false count_b,
    },
    {
      have count_c : count_in (u ++ v ^ 2 ++ x ++ y ^ 2 ++ z) c_ > n,
      {
        unfold list_n_times,
        simp [- list.append_assoc],
        repeat { rw count_in_append },
        have big_equality :
          count_in u c_ + (count_in v c_ + count_in v c_) + count_in x c_ + (count_in y c_ + count_in y c_) + count_in z c_ =
          (count_in u c_ + count_in v c_ + count_in x c_ + count_in y c_ + count_in z c_) + (count_in v c_ + count_in y c_),
        {
          ring,
        },
        rw big_equality,
        repeat { rw ← count_in_append },
        rw ← concatenating,
        repeat { rw count_in_append },
        rw count_in_repeat_eq c_,
        rw count_in_repeat_neq neq_ac,
        rw count_in_repeat_neq neq_bc,
        rw ← count_in_append,
        have at_least_one_c : count_in (v ++ y) c_ > 0,
        {
          --follows from `extra_c`
          sorry,
        },
        linarith,
      },
      rw count_a at hac,
      rw hac at count_c,
      exact has_lt.lt.false count_c,
    },
  },
  cases rest with no_b no_c,
  {
    -- prove the case `no_b` in the same way as the case `no_a` above
    sorry,
  },
  {
    -- prove the case `no_c` in the same way as the case `no_a` above
    sorry,
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
  intro ass,
  cases ass with hlea hlae,
  cases hlea with n₁ hlea_,
  cases hlea_ with m₁ h₁,
  cases hlae with n₂ hlae_,
  cases hlae_ with m₂ h₂,
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
