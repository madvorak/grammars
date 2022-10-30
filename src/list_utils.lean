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

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a)  ↔  (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a)  :=
by rw [list.forall_mem_append, list.forall_mem_append, and_assoc]

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

lemma take_join_of_lt {L : list (list α)} {n : ℕ} (notall : n < L.join.length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length, k < (L.nth_le m mlt).length ∧
    L.join.take n = (L.take m).join ++ (L.nth_le m mlt).take k :=
begin
  sorry
end

lemma drop_join_of_lt {L : list (list α)} {n : ℕ} (notall : n < L.join.length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length, k < (L.nth_le m mlt).length ∧
    L.join.drop n = (L.nth_le m mlt).drop k ++ (L.drop m.succ).join :=
begin
  sorry
end

-- should be added to mathlib
lemma reverse_join (L : list (list α)) :
  L.join.reverse = (list.map list.reverse L).reverse.join :=
begin
  induction L with l L' ih,
  {
    refl,
  },
  rw list.join,
  rw list.reverse_append,
  rw ih,
  rw list.map_cons,
  rw list.reverse_cons,
  rw list.join_append,
  rw list.join_singleton,
end

def n_times (l : list α) (n : ℕ) : list α :=
(list.repeat l n).join

infix ` ^ ` : 100 := n_times

end list_join

section countin

variables [decidable_eq α]

def count_in (l : list α) (a : α) : ℕ :=
list.sum (list.map (λ s, ite (s = a) 1 0) l)

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

lemma count_in_repeat_neq {a : α} {b : α} (hyp : a ≠ b) (n : ℕ) :
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

lemma count_in_append (a : α) :
  count_in (x ++ y) a  =  count_in x a  +  count_in y a  :=
begin
  unfold count_in,
  rw list.map_append,
  rw list.sum_append,
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
  exact nat.lt_asymm ih ih,
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
