-- Written by Patrick Johnson and released into the public domain at:
-- https://github.com/user7230724/lean-projects/blob/master/src/list_take_join/main.lean

import tactic

namespace list

variables {α : Type*}

private noncomputable def get_max [inhabited α] [linear_order α] (P : α → Prop) :=
classical.epsilon (λ (x : α), P x ∧ ∀ (y : α), x < y → ¬P y)

private lemma epsilon_eq [inhabited α] {P : α → Prop} {x : α}
  (h₁ : P x) (h₂ : ∀ (y : α), P y → y = x) : classical.epsilon P = x :=
begin
  have h₃ : P = (λ (y : α), y = x),
  { ext y, split; intro h₃,
    { exact h₂ y h₃ },
    { rwa h₃ }},
  subst h₃, apply classical.epsilon_singleton,
end

private lemma nat_get_max_spec {P : ℕ → Prop}
  (h₁ : ∃ (x : ℕ), P x) (h₂ : ∃ (x : ℕ), ∀ (y : ℕ), x ≤ y → ¬P y) :
  P (get_max P) ∧ ∀ (x : ℕ), get_max P < x → ¬P x :=
begin
  cases h₁ with m h₁, cases h₂ with n h₂, induction n with n ih,
  { cases h₂ m (zero_le m) h₁ },
  { simp_rw nat.succ_le_iff at h₂, by_cases h₃ : P n,
    { have : get_max P = n,
      { rw get_max, apply epsilon_eq,
        { use h₃, rintro k hk, exact h₂ k hk, },
        { rintro k ⟨h₄, h₅⟩, by_contra h₆,
          rw [←ne, ne_iff_lt_or_gt] at h₆, cases h₆,
          { cases h₅ n h₆ h₃ }, { cases h₂ k h₆ h₄ }}},
      rw this at *, clear this, exact ⟨h₃, h₂⟩ },
    { apply ih, rintro k hk, rw le_iff_eq_or_lt at hk, rcases hk with rfl | hk,
      { exact h₃ },
      { exact h₂ k hk }}},
end

lemma take_join_of_lt {L : list (list α)} {n : ℕ} (notall : n < L.join.length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length, k < (L.nth_le m mlt).length ∧
    L.join.take n = (L.take m).join ++ (L.nth_le m mlt).take k :=
begin
  generalize hX : L.length = X, symmetry' at hX,
  generalize hN : L.join.length = N, symmetry' at hN,
  rw ←hN at notall, have hl : L ≠ [],
  { rintro rfl, rw hN at notall, cases notall },
  generalize hP : (λ (m : ℕ), (L.take m).join.length ≤ n) = P, symmetry' at hP,
  generalize hm : get_max P = m, symmetry' at hm,
  generalize hk : n - (L.take m).join.length = k, symmetry' at hk,
  have hP0 : P 0, { rw hP, simp },
  have hPX : ∀ (r : ℕ), X ≤ r → ¬P r,
  { rintro r hr, rw hP, push_neg, convert notall, rw hX at hr,
    rw [hN, list.take_all_of_le hr] },
  obtain ⟨hm₁, hm₂⟩ := nat_get_max_spec ⟨0, hP0⟩ ⟨X, hPX⟩, rw ←hm at hm₁ hm₂,
  have hm₃ : ¬P m.succ := hm₂ _ (nat.lt_succ_self m),
  refine ⟨m, k, _, _, _⟩,
  { rw ←hX, by_contra' hx, cases hPX m hx hm₁ },
  { generalize_proofs h₁, rw hP at hm₁ hm₃, push_neg at hm₃,
    by_contra' hk₁, obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le hk₁,
    replace hk := congr_arg (λ (x : ℕ), x + (L.take m).join.length) hk,
    dsimp at hk, rw nat.sub_add_cancel hm₁ at hk, rw ←hk at hm₃,
    contrapose! hm₃, rw [add_comm, ←add_assoc], convert le_self_add,
    simp [nat.succ_eq_add_one, list.take_add, list.join_append, list.length_append],
    rw [list.take_one_drop_eq_of_lt_length, map_singleton, sum_singleton] },
  conv { to_lhs, rw [←list.take_append_drop m.succ L, list.join_append] },
  have hn₁ : (L.take m).join.length ≤ n, { rwa hP at hm₁ },
  have hn₂ : n < (L.take m.succ).join.length,
  { rw hP at hm₃, push_neg at hm₃, exact hm₃ },
  rw list.take_append_of_le_length (le_of_lt hn₂),
  change m.succ with m + 1, have hmX : m < X,
  { by_contra' hx, exact hPX m hx hm₁ },
  rw [list.take_add, list.join_append, list.take_one_drop_eq_of_lt_length,
    list.join, list.join, list.append_nil], swap, { rwa ←hX },
  have : n = (list.take m L).join.length + k,
  { rw hk, exact (nat.add_sub_of_le hn₁).symm },
  subst this, rw list.take_append,
end

end list
