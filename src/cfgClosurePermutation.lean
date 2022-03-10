import cfg


-- TODO maybe generalize it to bijections between types (two (possibly different) terminal alphabets)

def permute_lang {T : Type} (π : equiv.perm T) (L : language T) : language T :=
λ w : list T, list.map π.inv_fun w ∈ L

/-- The class of context-free languages is closed under permutation of terminals. -/
theorem CF_of_permute_CF {T : Type} (π : equiv.perm T) (L : language T) :
  is_CF L  →  is_CF (permute_lang π L)  :=
begin

  sorry,
end
