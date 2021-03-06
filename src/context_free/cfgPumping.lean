import context_free.cfg


def list_n_times {α : Type} (l : list α) (n : ℕ) : list α :=
(list.repeat l n).join

infix ` ^ ` : 100 := list_n_times


/-- Pumping lemma for context-free languages is not really an anxiom; its proof is missing. -/
axiom CF_pumping {T : Type} {L : language T} (cf : is_CF L) :
  ∃ n : ℕ, ∀ w ∈ L, list.length w ≥ n → (
    ∃ u v x y z : list T,
      (w = u ++ v ++ x ++ y ++ z) ∧
      (v ++ y).length > 0         ∧
      (v ++ x ++ y).length ≤ n    ∧
      (∀ i : ℕ, u ++ v ^ i ++ x ++ y ^ i ++ z ∈ L)
  )
