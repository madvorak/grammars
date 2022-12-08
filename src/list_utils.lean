import tactic

meta def in_list_explicit : tactic unit := `[
  tactic.repeat `[
    tactic.try `[apply list.mem_cons_self],
    tactic.try `[apply list.mem_cons_of_mem]
  ]
]

meta def split_ile : tactic unit := `[
  split,
  {
    in_list_explicit,
  }
]

namespace list

variables {α β : Type*} {x y z : list α}

section list_append_append

lemma length_append_append :
  list.length (x ++ y ++ z) = x.length + y.length + z.length :=
by rw [list.length_append, list.length_append]

lemma map_append_append {f : α → β} :
  list.map f (x ++ y ++ z) = list.map f x ++ list.map f y ++ list.map f z :=
by rw [list.map_append, list.map_append]

lemma filter_map_append_append {f : α → option β} :
  list.filter_map f (x ++ y ++ z) = list.filter_map f x ++ list.filter_map f y ++ list.filter_map f z :=
by rw [list.filter_map_append, list.filter_map_append]

lemma reverse_append_append :
  list.reverse (x ++ y ++ z) = z.reverse ++ y.reverse ++ x.reverse :=
by rw [list.reverse_append, list.reverse_append, list.append_assoc]

lemma mem_append_append {a : α} :
  a ∈ x ++ y ++ z  ↔  a ∈ x ∨ a ∈ y ∨ a ∈ z  :=
by rw [list.mem_append, list.mem_append, or_assoc]

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a)  ↔  (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a)  :=
by rw [list.forall_mem_append, list.forall_mem_append, and_assoc]

lemma join_append_append {X Y Z : list (list α)} :
  list.join (X ++ Y ++ Z) = X.join ++ Y.join ++ Z.join :=
by rw [list.join_append, list.join_append]

end list_append_append

section list_repeat

lemma repeat_zero (s : α) :
  list.repeat s 0 = [] :=
rfl

lemma repeat_succ_eq_singleton_append (s : α) (n : ℕ) :
  list.repeat s n.succ = [s] ++ list.repeat s n :=
rfl

lemma repeat_succ_eq_append_singleton (s : α) (n : ℕ) :
  list.repeat s n.succ = list.repeat s n ++ [s] :=
begin
  change list.repeat s (n + 1) = list.repeat s n ++ [s],
  rw list.repeat_add,
  refl,
end

end list_repeat

section list_join

lemma join_singleton : [x].join = x :=
by rw [list.join, list.join, list.append_nil]

lemma append_join_append (L : list (list α)) :
  x ++ (list.map (λ l, l ++ x) L).join = (list.map (λ l, x ++ l) L).join ++ x :=
begin
  induction L,
  {
    rw [list.map_nil, list.join, list.append_nil, list.map_nil, list.join, list.nil_append],
  },
  {
    rw [
      list.map_cons, list.join, list.map_cons, list.join,
      list.append_assoc, L_ih, list.append_assoc, list.append_assoc
    ],
  },
end

lemma reverse_join (L : list (list α)) :
  L.join.reverse = (list.map list.reverse L).reverse.join :=
begin
  induction L,
  {
    refl,
  },
  {
    rw [list.join, list.reverse_append, L_ih, list.map_cons, list.reverse_cons, list.join_append, list.join_singleton],
  },
end

-- copied from `https://github.com/user7230724/lean-projects/blob/master/src/list_take_join/main.lean`
-- TODO refactor and cite the author by their name
noncomputable theory
open_locale classical
private def get_max [inhabited α] [linear_order α] (P : α → Prop) :=
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
private lemma list.take_eq_take {l : list α} {m n : ℕ} :
  l.take m = l.take n ↔ min m l.length = min n l.length :=
begin
  induction l with x l ih generalizing m n,
  { simp },
  { simp_rw list.length_cons, split; intro h,
    { cases n, { simp at h, subst h },
      cases m, { simp at h, cases h },
      simp only [list.take, eq_self_iff_true, true_and] at h,
      simpa [nat.min_succ_succ] using ih.mp h },
    { cases n, { simp at h, subst h },
      cases m, { simp [nat.min_succ_succ] at h, cases h },
      simp_rw nat.min_succ_succ at h, simpa using ih.mpr h }},
end
private lemma list.take_add {l : list α} {m n : ℕ} :
  l.take (m + n) = l.take m ++ (l.drop m).take n :=
begin
  convert_to
    list.take (m + n) (list.take m l ++ list.drop m l) =
    list.take m l ++ list.take n (list.drop m l),
  { rw list.take_append_drop },
  rw [list.take_append_eq_append_take, list.take_all_of_le,
    list.append_right_inj], swap,
  { transitivity m,
    { apply list.length_take_le },
    { simp }},
  simp only [list.take_eq_take, list.length_take, list.length_drop],
  generalize : l.length = k, by_cases h : m ≤ k,
  { simp [min_eq_left_iff.mpr h] },
  { push_neg at h, simp [nat.sub_eq_zero_of_le (le_of_lt h)] },
end
private lemma list.take_one_drop_eq_of_lt_length {l : list α} {n : ℕ}
  (h : n < l.length) : (l.drop n).take 1 = [l.nth_le n h] :=
begin
  induction l with x l ih generalizing n,
  { cases h },
  { by_cases h₁ : l = [],
    { subst h₁, rw list.nth_le_singleton, simp at h, subst h, simp },
    have h₂ := h, rw [list.length_cons, nat.lt_succ_iff, le_iff_eq_or_lt] at h₂,
    cases n, { simp }, rw [list.drop, list.nth_le], apply ih },
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
    list.join_singleton], swap, { rwa ←hX },
  have : n = (list.take m L).join.length + k,
  { rw hk, exact (nat.add_sub_of_le hn₁).symm },
  subst this, rw list.take_append,
end
-- end of copied code

private lemma last_lemma {m : ℕ} (mlt : m < x.length) :
  drop m x = x.nth_le m mlt :: drop m.succ x :=
begin
  induction x with d l ih generalizing m,
  {
    exfalso,
    rw length at mlt,
    exact nat.not_lt_zero m mlt,
  },
  rw drop,
  cases m,
  {
    simp,
  },
  rw [drop, nth_le],
  apply ih,
end

lemma drop_join_of_lt {L : list (list α)} {n : ℕ} (notall : n < L.join.length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length, k < (L.nth_le m mlt).length ∧
    L.join.drop n = (L.nth_le m mlt).drop k ++ (L.drop m.succ).join :=
begin
  obtain ⟨m, k, mlt, klt, left_half⟩ := take_join_of_lt notall,
  use    [m, k, mlt, klt],
  have L_two_parts := congr_arg list.join (list.take_append_drop m L),
  rw list.join_append at L_two_parts,
  have whole := list.take_append_drop n L.join,
  rw left_half at whole,
  have important := eq.trans whole L_two_parts.symm,
  rw append_assoc at important,
  have right_side := append_left_cancel important,
  have auxi : (drop m L).join = (L.nth_le m mlt :: drop m.succ L).join,
  {
    apply congr_arg,
    apply last_lemma,
  },
  rw join at auxi,
  rw auxi at right_side,
  have near_result :
    take k (L.nth_le m mlt) ++ drop n L.join =
    take k (L.nth_le m mlt) ++ drop k (L.nth_le m mlt) ++ (drop m.succ L).join,
  {
    convert right_side,
    rw list.take_append_drop,
  },
  rw append_assoc at near_result,
  exact append_left_cancel near_result,
end

def n_times (l : list α) (n : ℕ) : list α :=
(list.repeat l n).join

infix ` ^ ` : 100 := n_times

end list_join

variables [decidable_eq α]

section list_index_of

lemma index_of_append_of_notin {a : α} (not_on_left : a ∉ x) :
  index_of a (x ++ y)  =  x.length  +  index_of a y  :=
begin
  induction x with d l ih,
  {
    rw [list.nil_append, list.length, zero_add],
  },
  rw [
    list.cons_append,
    index_of_cons_ne _ (ne_of_not_mem_cons not_on_left),
    list.length,
    ih (not_mem_of_not_mem_cons not_on_left),
    nat.succ_add
  ],
end

end list_index_of

section countin

def count_in (l : list α) (a : α) : ℕ :=
list.sum (list.map (λ s, ite (s = a) 1 0) l)

lemma count_in_nil (a : α) :
  count_in [] a = 0 :=
begin
  refl,
end

lemma count_in_cons (a b : α) :
  count_in (b :: x) a  =  ite (b = a) 1 0  +  count_in x a  :=
begin
  unfold count_in,
  rw list.map_cons,
  rw list.sum_cons,
end

lemma count_in_append (a : α) :
  count_in (x ++ y) a  =  count_in x a  +  count_in y a  :=
begin
  unfold count_in,
  rw list.map_append,
  rw list.sum_append,
end

lemma count_in_repeat_eq (a : α) (n : ℕ) :
  count_in (list.repeat a n) a  =  n  :=
begin
  unfold count_in,
  induction n with m ih,
  {
    refl,
  },
  rw [list.repeat_succ, list.map_cons, list.sum_cons, ih],
  rw if_pos rfl,
  apply nat.one_add,
end

lemma count_in_repeat_neq {a b : α} (hyp : a ≠ b) (n : ℕ) :
  count_in (list.repeat a n) b  =  0  :=
begin
  unfold count_in,
  induction n with m ih,
  {
    refl,
  },
  rw [list.repeat_succ, list.map_cons, list.sum_cons, ih, add_zero],
  rw ite_eq_right_iff,
  intro impos,
  exfalso,
  exact hyp impos,
end

lemma count_in_singleton_eq (a : α) :
  count_in [a] a  =  1  :=
begin
  exact count_in_repeat_eq a 1,
end

lemma count_in_singleton_neq {a b : α} (hyp : a ≠ b) :
  count_in [a] b  =  0  :=
begin
  exact count_in_repeat_neq hyp 1,
end

lemma count_in_pos_of_in {a : α} (hyp : a ∈ x) :
  count_in x a > 0 :=
begin
  induction x with d l ih,
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
  have zero_in_tail : count_in l a = 0,
  {
    unfold count_in,
    exact contr.right,
  },
  rw zero_in_tail at ih,
  exact nat.lt_irrefl 0 ih,
end

lemma count_in_zero_of_notin {a : α} (hyp : a ∉ x) :
  count_in x a = 0 :=
begin
  induction x with d l ih,
  {
    refl,
  },
  unfold count_in,
  rw [list.map_cons, list.sum_cons, add_eq_zero_iff, ite_eq_right_iff],
  split,
  {
    simp only [nat.one_ne_zero],
    exact (list.ne_of_not_mem_cons hyp).symm,
  },
  {
    exact ih (list.not_mem_of_not_mem_cons hyp),
  },
end

lemma count_in_join (L : list (list α)) (a : α) :
  count_in L.join a = list.sum (list.map (λ w, count_in w a) L) :=
begin
  induction L,
  {
    refl,
  },
  {
    rw [list.join, count_in_append, list.map, list.sum_cons, L_ih],
  },
end

end countin

end list
