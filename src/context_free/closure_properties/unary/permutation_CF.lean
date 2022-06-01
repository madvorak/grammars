import context_free.closure_properties.unary.bijection_CF


/-- The class of context-free languages is closed under permutation of terminals. -/
theorem CF_of_permute_CF {T : Type} (π : equiv.perm T) (L : language T) :
  is_CF L  →  is_CF (permute_lang π L)  :=
CF_of_bijemap_CF π L
