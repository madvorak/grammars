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

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a)  ↔  (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a)  :=
by rw [ list.forall_mem_append, list.forall_mem_append, and_assoc ]

lemma reverse_append_append :
  list.reverse (x ++ y ++ z) = z.reverse ++ y.reverse ++ x.reverse :=
by rw [ list.reverse_append, list.reverse_append, list.append_assoc ]

end list


namespace prod

variables (t : α × β × γ)

@[simp] def first : α := t.fst
@[simp] def secon : β := t.snd.fst
@[simp] def third : γ := t.snd.snd

def firstwo : α × β := (t.first, t.secon)

end prod
