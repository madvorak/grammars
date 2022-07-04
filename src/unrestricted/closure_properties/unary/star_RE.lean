import unrestricted.grammarLiftSink



-- new nonterminal type
private def nnn (T N : Type) : Type :=
(option N) ⊕ (fin 2 × T)

variable {T : Type}

private def wrap_symbol {N : Type} (parity : fin 2) : symbol T N → symbol T (nnn T N)
| (symbol.terminal t)    := symbol.nonterminal (sum.inr (parity, t))
| (symbol.nonterminal n) := symbol.nonterminal (sum.inl (some n))

private def wrap_grule {N : Type} (parity : fin 2) (r : grule T N) : grule T (nnn T N) :=
grule.mk (
    list.map (wrap_symbol parity) r.input_string.first,
    sum.inl (some r.input_string.secon),
    list.map (wrap_symbol parity) r.input_string.third)
  (list.map (wrap_symbol parity) r.output_string)

private def all_used_terminals (g : grammar T) : list T :=
[] -- TODO

private def rules_for_individual_terminals (parity : fin 2) (g : grammar T) : list (grule T (nnn T g.nt)) :=
(list.map (λ t, grule.mk ([], sum.inr (parity, t), []) [symbol.terminal t]) (all_used_terminals g))

-- TODO distinguish between nonterminals of odd vs even parts
private def star_grammar (g : grammar T) : grammar T :=
grammar.mk (nnn T g.nt) (sum.inl none) (
    (grule.mk ([], sum.inl none, []) []) ::
    (grule.mk ([], sum.inl none, []) [
        symbol.nonterminal (sum.inl (some g.initial)),
        symbol.nonterminal (sum.inl none)
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
