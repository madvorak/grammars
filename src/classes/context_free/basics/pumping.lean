import classes.context_free.basics.definition

namespace grammars

/-- Pumping lemma for context-free languages. -/
lemma CF_pumping {T : Type} {L : language T} (cf : is_CF L) :
  ∃ n : ℕ, ∀ w ∈ L, list.length w ≥ n → (
    ∃ u v x y z : list T,
      (w = u ++ v ++ x ++ y ++ z) ∧
      (v ++ y).length > 0         ∧
      (v ++ x ++ y).length ≤ n    ∧
      (∀ i : ℕ, u ++ v ^ i ++ x ++ y ^ i ++ z ∈ L)
  ) :=
sorry

end grammars