import unrestricted.closure_properties.binary.RE_concatenation_RE


-- new nonterminal type
private def nn (N : Type) : Type :=
N ⊕ fin 3
/-
`0` represents the new starting symbol `Z`
`1` represents the delimiter `#`
`2` represents the nonterminal `R` responsible for final rewriting
-/

-- new symbol type
private def ns (T N : Type) : Type :=
symbol T (nn N)


variables {T : Type}

private def wrap_symbol {N : Type} : symbol T N → ns T N
| (symbol.terminal t)    := symbol.terminal t
| (symbol.nonterminal n) := symbol.nonterminal (sum.inl n)


private def star_grammar (g : grammar T) : grammar T :=
grammar.mk
  (nn g.nt)
  (sum.inr 0)
  ((grule.mk [] (sum.inr 0) [] [ -- `Z → ZS#`
    symbol.nonterminal (sum.inr 0),
    symbol.nonterminal (sum.inl g.initial),
    symbol.nonterminal (sum.inr 1)]
  ) :: sorry)


/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : language T) :
  is_RE L  →  is_RE L.star  :=
begin
  rintro ⟨g₀, hg₀⟩,
  use star_grammar g₀,
  sorry,
end
