import tactic

variables {α β γ : Type*}


namespace list

variables {x y z : list α}

lemma map_append_append {f : α → β} :
  list.map f (x ++ y ++ z) = list.map f x ++ list.map f y ++ list.map f z :=
by rw [ list.map_append, list.map_append ]

lemma filter_map_append_append {f : α → option γ} :
  list.filter_map f (x ++ y ++ z) = list.filter_map f x ++ list.filter_map f y ++ list.filter_map f z :=
by rw [ list.filter_map_append, list.filter_map_append ]

lemma length_append_append :
  list.length (x ++ y ++ z) = x.length + y.length + z.length :=
by rw [ list.length_append, list.length_append ]

lemma reverse_append_append :
  list.reverse (x ++ y ++ z) = z.reverse ++ y.reverse ++ x.reverse :=
by rw [ list.reverse_append, list.reverse_append, list.append_assoc ]

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a)  ↔  (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a)  :=
by rw [ list.forall_mem_append, list.forall_mem_append, and_assoc ]


section todo_move_elsewhere

lemma two_singletons_of_doubleton {α : Type} {a b : α} : [a, b] = [a] ++ [b] :=
rfl

lemma append_singleton_of_cons {α : Type} (a : α) (l : list α) : a :: l = [a] ++ l :=
rfl

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

lemma nth_eq_nth_of_nth_le_eq_nth_le
  {i j : ℕ} {ix : i < x.length} {jy : j < y.length}
  (h : x.nth_le i ix = y.nth_le j jy) :
  x.nth i = y.nth j :=
by rw [list.nth_le_nth ix, list.nth_le_nth jy, h]

end todo_move_elsewhere

end list


namespace prod

variables (t : α × β × γ)

def first : α := t.fst
def secon : β := t.snd.fst
def third : γ := t.snd.snd

end prod
