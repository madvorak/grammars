import unrestricted.grammarLiftSink


variable {T : Type}

private def wrap_symbol {N : Type} : symbol T N → symbol T (option N)
| (symbol.terminal t)    := symbol.terminal t
| (symbol.nonterminal n) := symbol.nonterminal (option.some n)

private def wrap_grule {N : Type} : grule T N → grule T (option N)
| (grule.mk (x, y, z) o) := grule.mk
    (list.map wrap_symbol x, option.some y, list.map wrap_symbol z)
    (list.map wrap_symbol o)

private def star_grammar (g : grammar T) : grammar T :=
grammar.mk (option g.nt) none (
    (grule.mk ([], none, []) ([])) ::
    (grule.mk ([], none, []) ([symbol.nonterminal (option.some g.initial), symbol.nonterminal none])) ::
    (list.map wrap_grule g.rules)
  )

/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : language T) :
  is_RE L  →  is_RE L.star  :=
begin
  intro ass,
  cases ass with g₀ hyp,
  let g := star_grammar g₀,
  sorry,
end


private def asdf_grule {N : Type} (r : grule T N) : grule T (option N) :=
grule.mk
  (
    list.map wrap_symbol r.input_string.first, 
    option.some r.input_string.secon,
    list.map wrap_symbol r.input_string.third
  )
  (list.map wrap_symbol r.output_string)

private lemma the_same {N : Type} : @wrap_grule T N = @asdf_grule T N :=
begin
  ext1 r,
  rcases r with ⟨ ⟨x, y, z⟩, o⟩,
  refl,
end
