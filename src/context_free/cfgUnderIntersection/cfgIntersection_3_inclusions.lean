import context_free.cfgUnderIntersection.cfgIntersection_1_basic


lemma intersection_of_lang_eq_eq {w : list (fin 3)} :
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


private lemma qwerty (n₁ m₁ n₂ m₂ : ℕ) (n₁pos : n₁ > 0)
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

lemma lang_eq_eq_of_intersection {w : list (fin 3)} :
  w ∈ lang_eq_any ⊓ lang_any_eq  →  w ∈ lang_eq_eq :=
begin
  rintro ⟨ ⟨ n₁, m₁, h₁ ⟩, ⟨ n₂, m₂, h₂ ⟩ ⟩,
  have equ := eq.trans h₁.symm h₂,

  by_cases hn₁ : n₁ = 0,
  {
    have hn₂ : n₂ = 0,
      sorry, -- follows from `hn₁` using `equ`
    have hm₂ : m₂ = 0,
      sorry, -- follows from `hn₁` using `equ`
    use 0,
    rw hn₂ at h₂,
    rw hm₂ at h₂,
    exact h₂,
  },

  have n₁pos : n₁ > 0 :=
    pos_iff_ne_zero.mpr hn₁,
  have n₂pos : n₂ > 0,
    sorry, -- follows from `n₁pos` using `equ`
  have m₂pos : m₂ > 0,
    sorry, -- follows from `n₁pos` using `equ`
  have m₁pos : m₁ > 0,
    sorry, -- follows from `m₂pos` using `equ`
  clear hn₁,

  have n_ge : n₁ ≥ n₂,
  {

    sorry,
  },
  have n_le : n₁ ≤ n₂,
  {
    exact qwerty n₁ m₁ n₂ m₂ n₁pos a_ b_ c_ (by dec_trivial) (by dec_trivial) equ,
  },
  have m_ge : m₁ ≥ m₂,
  {
    have rev := congr_arg list.reverse equ,
    clear equ,
    repeat { rw list.reverse_append at rev },
    repeat { rw list.reverse_repeat at rev },
    rw ← list.append_assoc at rev,
    rw ← list.append_assoc at rev,
    apply qwerty m₂ n₂ m₁ n₁ m₂pos c_ b_ a_ (by dec_trivial) (by dec_trivial) rev.symm,
  },
  have m_le : m₁ ≤ m₂,
  {
    have rev := congr_arg list.reverse equ,
    clear equ,
    repeat { rw list.reverse_append at rev },
    repeat { rw list.reverse_repeat at rev },
    rw ← list.append_assoc at rev,
    rw ← list.append_assoc at rev,
    apply qwerty m₁ n₁ m₂ n₂ m₁pos c_ b_ a_ (by dec_trivial) (by dec_trivial),

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
