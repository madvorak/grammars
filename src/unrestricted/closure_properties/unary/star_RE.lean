import unrestricted.closure_properties.binary.RE_concatenation_RE


-- new nonterminal type
private def nn (T N : Type) : Type :=
option (fin 2 × (N ⊕ T))

variables {T : Type}

private def wrap_symbol {N : Type} (parity : fin 2) : symbol T N → symbol T (nn T N)
| (symbol.terminal t)    := symbol.nonterminal (some (parity, sum.inr t))
| (symbol.nonterminal n) := symbol.nonterminal (some (parity, sum.inl n))


/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : language T) :
  is_RE L  →  is_RE L.star  :=
begin
  rintro ⟨g₀, hg₀⟩,
  sorry,
end
