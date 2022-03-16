import context_free.closure_properties.binary.CF_union_CF


variable {T : Type}

/-- The class of context-free languages is closed under the Kleene star. -/
theorem CF_of_star_CF (L : language T) :
  is_CF L  →  is_CF L.star  :=
begin
  sorry,
end
