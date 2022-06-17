import tactic

variables {α β γ : Type*}


namespace list

lemma filter_map_join (f : α → option β) (l : list (list α)) :
  filter_map f (join l) = join (map (filter_map f) l) :=
begin
  induction l with d t ih,
  {
    refl,
  },
  {
    rw [ map, join, join, filter_map_append, ih ],
  },
end

variables {x y z : list α}

lemma map_append_append {f : α → β} :
  list.map f (x ++ y ++ z) = list.map f x ++ list.map f y ++ list.map f z :=
by rw [ list.map_append, list.map_append ]

lemma filter_map_append_append {f : α → option γ} :
  list.filter_map f (x ++ y ++ z) = list.filter_map f x ++ list.filter_map f y ++ list.filter_map f z :=
by rw [ list.filter_map_append, list.filter_map_append ]

lemma reverse_append_append :
  list.reverse (x ++ y ++ z) = z.reverse ++ y.reverse ++ x.reverse :=
by rw [ list.reverse_append, list.reverse_append, list.append_assoc ]

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a)  ↔  (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a)  :=
by rw [ list.forall_mem_append, list.forall_mem_append, and_assoc ]

end list


namespace prod

variables (t : α × β × γ)

@[simp] def first : α := t.fst
@[simp] def secon : β := t.snd.fst
@[simp] def third : γ := t.snd.snd

end prod
