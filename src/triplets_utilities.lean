import tactic

variables {α β γ : Type*}


namespace list

variables {x y z : list α}

lemma map_append_append {f : α → β} :
  list.map f (x ++ y ++ z) = list.map f x ++ list.map f y ++ list.map f z :=
by rw [list.map_append, list.map_append]

lemma filter_map_append_append {f : α → option γ} :
  list.filter_map f (x ++ y ++ z) = list.filter_map f x ++ list.filter_map f y ++ list.filter_map f z :=
by rw [list.filter_map_append, list.filter_map_append]

lemma length_append_append :
  list.length (x ++ y ++ z) = x.length + y.length + z.length :=
by rw [list.length_append, list.length_append]

lemma reverse_append_append :
  list.reverse (x ++ y ++ z) = z.reverse ++ y.reverse ++ x.reverse :=
by rw [list.reverse_append, list.reverse_append, list.append_assoc]

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a)  ↔  (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a)  :=
by rw [list.forall_mem_append, list.forall_mem_append, and_assoc]


section todo_move_elsewhere

lemma two_singletons_of_doubleton {a b : α} : [a, b] = [a] ++ [b] :=
rfl

lemma append_singleton_of_cons (a : α) (l : list α) : a :: l = [a] ++ l :=
rfl

lemma take_one_eq_singleton {l : list α} (nonempty : 0 < l.length):
  list.take 1 l = [l.nth_le 0 nonempty] :=
begin
  cases l with d x,
  {
    exfalso,
    unfold length at nonempty,
    exact false_of_ne (ne_of_lt nonempty),
  },
  {
    refl,
  },
end

lemma take_one_drop {l : list α} {i : ℕ} (hil : i < l.length) :
  list.take 1 (list.drop i l) = [l.nth_le i hil] :=
begin
  have l_split : l = take i l ++ drop i l,
  {
    rw take_append_drop,
  },
  rw nth_le_of_eq l_split,
  rw nth_le_append_right,
  {
    have smaller_i : min i l.length = i,
    {
      exact min_eq_left (le_of_lt hil),
    },
    norm_num,
    simp only [smaller_i, tsub_self],
    apply take_one_eq_singleton,
  },
  {
    norm_num,
  },
end

lemma drop_take_succ {l : list α} {i : ℕ} (hil : i < l.length) :
  list.drop i (list.take (i + 1) l) = [l.nth_le i hil] :=
begin
  rw drop_take,
  apply take_one_drop,
end

-- version for mathlib (TODO refactor)
theorem length_filter_map (f : α → option β) (l : list α) :
  (filter_map f l).length ≤ l.length :=
begin
  induction l with hd tl ih,
  { refl },
  { rw length,
    unfold filter_map,
    cases f hd,
    { change (filter_map f tl).length ≤ tl.length + 1,
      apply le_trans ih,
      apply nat.le_succ },
    { change (val :: (filter_map f tl)).length ≤ tl.length + 1,
      rw length,
      apply add_le_add_right,
      exact ih } }
end

end todo_move_elsewhere

end list


namespace prod

variables (t : α × β × γ)

def first : α := t.fst
def secon : β := t.snd.fst
def third : γ := t.snd.snd

end prod
