import unrestricted.grammarLiftSink


-- new nonterminal type
private def nn (T N : Type) : Type :=
option (fin 2 × (N ⊕ T))

variable {T : Type}

private def wrap_symbol {N : Type} (parity : fin 2) : symbol T N → symbol T (nn T N)
| (symbol.terminal t)    := symbol.nonterminal (some (parity, sum.inr t))
| (symbol.nonterminal n) := symbol.nonterminal (some (parity, sum.inl n))

private def wrap_grule {N : Type} (parity : fin 2) (r : grule T N) : grule T (nn T N) :=
grule.mk (
    list.map (wrap_symbol parity) r.input_string.first,
    some (parity, sum.inl r.input_string.secon),
    list.map (wrap_symbol parity) r.input_string.third)
  (list.map (wrap_symbol parity) r.output_string)

private def all_used_terminals (g : grammar T) : list T :=
[] -- TODO (ditto in `RE_concatenation_RE.lean`)

private def rules_for_individual_terminals (parity : fin 2) (g : grammar T) : list (grule T (nn T g.nt)) :=
list.map (λ t, grule.mk ([], some (parity, sum.inr t), []) [symbol.terminal t]) (all_used_terminals g)

private def star_grammar (g : grammar T) : grammar T :=
grammar.mk (nn T g.nt) none (
    (grule.mk ([], none, []) []) ::
    (grule.mk ([], none, []) [
        symbol.nonterminal (some (0, sum.inl g.initial))
      ]) ::
    (grule.mk ([], none, []) [
        symbol.nonterminal (some (0, sum.inl g.initial)),
        symbol.nonterminal (some (1, sum.inl g.initial)),
        symbol.nonterminal none
      ]) ::
    ((list.map (wrap_grule 0) g.rules) ++ (list.map (wrap_grule 1) g.rules)) ++
    ((rules_for_individual_terminals 0 g) ++ (rules_for_individual_terminals 1 g))
  )


/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : language T) :
  is_RE L  →  is_RE L.star  :=
begin
  rintro ⟨ g₀, hg₀ ⟩,
  use star_grammar g₀,
  rw ← hg₀,
  ext1 w,
  split,
  {
    sorry,
  },
  {
    sorry,
  },
end
