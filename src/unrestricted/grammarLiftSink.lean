import unrestricted.grammar


variables {T : Type}

def lift_symbol_ {N₀ N : Type} (lift_N : N₀ → N) : symbol T N₀ → symbol T N
| (symbol.terminal ter) := symbol.terminal ter
| (symbol.nonterminal nonter) := symbol.nonterminal (lift_N nonter)

def sink_symbol_ {N₀ N : Type} (sink_N : N → option N₀) : symbol T N → option (symbol T N₀)
| (symbol.terminal ter) := some (symbol.terminal ter)
| (symbol.nonterminal nonter) := option.map symbol.nonterminal (sink_N nonter)

def lift_string_ {N₀ N : Type} (lift_N : N₀ → N) :
  list (symbol T N₀) → list (symbol T N) :=
list.map (lift_symbol_ lift_N)

def sink_string_ {N₀ N : Type} (sink_N : N → option N₀) :
  list (symbol T N) → list (symbol T N₀) :=
list.filter_map (sink_symbol_ sink_N)

def lift_rule_ {N₀ N : Type} (lift_N : N₀ → N) :
  grule T N₀ → grule T N :=
λ r : grule T N₀,
  ⟨ (lift_string_ lift_N r.input_string.first, lift_N r.input_string.secon, lift_string_ lift_N r.input_string.third),
    lift_string_ lift_N r.output_string ⟩

structure lifted_grammar_ :=
(g₀ g : grammar T)
(lift_nt : g₀.nt → g.nt)
(lift_inj : function.injective lift_nt)
(corresponding_rules : ∀ r : grule T g₀.nt,
  r ∈ g₀.rules →
    lift_rule_ lift_nt r ∈ g.rules
)
(preimage_of_rules : ∀ r : grule T g.nt,
  (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, lift_nt n₀ = r.input_string.secon) →
    (∃ r₀ ∈ g₀.rules, lift_rule_ lift_nt r₀ = r)
)
(sink_nt : g.nt → option g₀.nt)
(sink_inj : ∀ x y, sink_nt x = sink_nt y →
  x = y  ∨  sink_nt x = none
)
(lift_nt_sink : ∀ n₀ : g₀.nt, sink_nt (lift_nt n₀) = some n₀)






def good_letter_ {lg : @lifted_grammar_ T} : symbol T lg.g.nt → Prop
| (symbol.terminal t)     := true
| (symbol.nonterminal nt) := ∃ n₀ : lg.g₀.nt, lg.sink_nt nt = n₀

def good_string_ {lg : @lifted_grammar_ T} (str : list (symbol T lg.g.nt)) :=
∀ letter ∈ str, good_letter_ letter



lemma lift_deri_
    (lg : lifted_grammar_)
    (input output : list (symbol T lg.g₀.nt))
    (hyp : grammar_derives lg.g₀ input output) :
  grammar_derives lg.g (lift_string_ lg.lift_nt input) (lift_string_ lg.lift_nt output) :=
begin
  sorry,
end


lemma sink_deri_
    (lg : lifted_grammar_)
    (input output : list (symbol T lg.g.nt))
    (hyp : grammar_derives lg.g input output)
    (ok_input : good_string_ input) :
  grammar_derives lg.g₀ (sink_string_ lg.sink_nt input) (sink_string_ lg.sink_nt output)
  ∧ good_string_ output :=
begin
  sorry,
end







