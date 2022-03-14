import cfgClosureConcatenation
import cfgClosureUnion


variable {T : Type}

lemma CF_of_pow_CF (L : language T) (exponent : ℕ) :
  is_CF L  →  is_CF (L ^ exponent) :=
begin
  intro cfL,
  induction exponent with n ih,
  {
    -- TODO (afaik the language that contains only the empty word)
    use cfg_empty_word,
    
    sorry,
  },
  rw pow_succ',
  exact CF_of_CF_c_CF (L ^ n) L (and.intro ih cfL),
end

/-- The class of context-free languages is closed under the Kleene star. -/
theorem CF_of_star_CF (L : language T) :
  is_CF L  →  is_CF L.star  :=
begin
  intro cfL,
  rw language.star_eq_supr_pow,
  apply CF_of_infiniteUnion_CF,
  intro i,
  exact CF_of_pow_CF L i cfL,
end
