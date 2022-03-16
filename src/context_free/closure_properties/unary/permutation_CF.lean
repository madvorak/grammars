import context_free.closure_properties.unary.bijection_CF


variable {T : Type}

def permute_lang (π : equiv.perm T) (L : language T) : language T :=
bijemap_lang π L

/-- The class of context-free languages is closed under permutation of terminals. -/
theorem CF_of_permute_CF (π : equiv.perm T) (L : language T) :
  is_CF L  →  is_CF (permute_lang π L)  :=
CF_of_bijemap_CF π L
