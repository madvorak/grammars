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

end list


namespace prod

def first (t : α × β × γ) : α := t.fst
def secon (t : α × β × γ) : β := t.snd.fst
def third (t : α × β × γ) : γ := t.snd.snd

end prod
