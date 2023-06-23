import tactic
import utilities.written_by_others.list_take_join

section tactic_in_list_explicit

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

end tactic_in_list_explicit

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

section list_replicate

lemma replicate_succ_eq_singleton_append (s : α) (n : ℕ) :
  list.replicate n.succ s = [s] ++ list.replicate n s :=
begin
  refl,
end

lemma replicate_succ_eq_append_singleton (s : α) (n : ℕ) :
  list.replicate n.succ s = list.replicate n s ++ [s] :=
begin
  change list.replicate (n + 1) s = list.replicate n s ++ [s],
  rw list.replicate_add,
  refl,
end

end list_replicate

section list_join

private lemma cons_drop_succ {m : ℕ} (mlt : m < x.length) :
  drop m x = x.nth_le m mlt :: drop m.succ x :=
begin
  induction x with d l ih generalizing m,
  {
    exfalso,
    rw length at mlt,
    exact nat.not_lt_zero m mlt,
  },
  cases m,
  {
    simp,
  },
  rw [drop, drop, nth_le],
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
    apply cons_drop_succ,
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
(list.replicate n l).join

infix ` ^^ ` : 100 := n_times

end list_join

variables [decidable_eq α]

section list_count_in

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

lemma count_in_replicate_eq (a : α) (n : ℕ) :
  count_in (list.replicate n a) a  =  n  :=
begin
  unfold count_in,
  induction n with m ih,
  {
    refl,
  },
  rw [list.replicate_succ, list.map_cons, list.sum_cons, ih],
  rw if_pos rfl,
  apply nat.one_add,
end

lemma count_in_replicate_neq {a b : α} (hyp : a ≠ b) (n : ℕ) :
  count_in (list.replicate n a) b  =  0  :=
begin
  unfold count_in,
  induction n with m ih,
  {
    refl,
  },
  rw [list.replicate_succ, list.map_cons, list.sum_cons, ih, add_zero],
  rw ite_eq_right_iff,
  intro impos,
  exfalso,
  exact hyp impos,
end

lemma count_in_singleton_eq (a : α) :
  count_in [a] a  =  1  :=
begin
  exact list.count_in_replicate_eq a 1,
end

lemma count_in_singleton_neq {a b : α} (hyp : a ≠ b) :
  count_in [a] b  =  0  :=
begin
  exact list.count_in_replicate_neq hyp 1,
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
  rw le_zero_iff at contr,
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
    rw [list.join, list.count_in_append, list.map, list.sum_cons, L_ih],
  },
end

end list_count_in

end list
