import tactic

meta def in_list_explicit : tactic unit := `[
  tactic.repeat `[
    tactic.try `[apply list.mem_cons_self],
    tactic.try `[apply list.mem_cons_of_mem]
  ]
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
begin
  refl,
end

lemma repeat_succ_eq_singleton_append (s : α) (n : ℕ) :
  list.repeat s n.succ = [s] ++ list.repeat s n :=
begin
  -- almost the same as `list.repeat_succ` which is a `rfl` lemma
  refl,
end

lemma repeat_succ_eq_append_singleton (s : α) (n : ℕ) :
  list.repeat s n.succ = list.repeat s n ++ [s] :=
begin
  change list.repeat s (n + 1) = list.repeat s n ++ [s],
  rw list.repeat_add,
  refl,
end

end list_repeat

end list
