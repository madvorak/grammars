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

private def wrap_sym {N : Type} : symbol T N → ns T N
| (symbol.terminal t)    := symbol.terminal t
| (symbol.nonterminal n) := symbol.nonterminal (sum.inl n)

private def wrap_gr {N : Type} (r : grule T N) : grule T (nn N) :=
grule.mk
  (list.map wrap_sym r.input_L)
  (sum.inl r.input_N)
  (list.map wrap_sym r.input_R)
  (list.map wrap_sym r.output_string)

private def rules_for_scanning_terminals (g : grammar T) : list (grule T (nn g.nt)) :=
list.map (λ t, -- `Rt → tR`
    grule.mk [] (sum.inr 2) [symbol.terminal t] [symbol.terminal t, symbol.nonterminal (sum.inr 2)]
  ) (all_used_terminals g)

-- based on `/informal/KleeneStar.pdf`
private def star_grammar (g : grammar T) : grammar T :=
grammar.mk
  (nn g.nt)
  (sum.inr 0)
  (
    (grule.mk [] (sum.inr 0) [] [ -- `Z → ZS#`
      symbol.nonterminal (sum.inr 0),
      symbol.nonterminal (sum.inl g.initial),
      symbol.nonterminal (sum.inr 1)]
    ) :: (grule.mk [] (sum.inr 0) [] [ -- `Z → R#`
      symbol.nonterminal (sum.inr 2),
      symbol.nonterminal (sum.inr 1)]
    ) :: (grule.mk [] (sum.inr 2) [symbol.nonterminal (sum.inr 1)] [ -- `R# → R`
      symbol.nonterminal (sum.inr 2)]
    ) :: (grule.mk [] (sum.inr 0) [] [ -- `R# → ∅`
    ]) :: list.map wrap_gr g.rules ++ 
    rules_for_scanning_terminals g)


/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : language T) :
  is_RE L  →  is_RE L.star  :=
begin
  rintro ⟨g₀, hg₀⟩,
  use star_grammar g₀,
  sorry,
end
