import cfgClosureConcatenation


variable {T : Type}

def lang_pow (L : language T) (exponent : ℕ) : language T :=
{ x | ∃ lili : list (list T), lili.length = exponent ∧ x = lili.join ∧ ∀ w ∈ lili, w ∈ L}

lemma CF_of_pow_CF (L : language T) (exponent : ℕ) :
  is_CF L  →  is_CF (lang_pow L exponent) :=
begin
  intro cfL,
  
  sorry,
end

/-- The class of context-free languages is closed under the Kleene star. -/
theorem CF_of_star_CF (L : language T) :
  is_CF L  →  is_CF L.star  :=
begin
  intro cfL,
  
  sorry,
end
