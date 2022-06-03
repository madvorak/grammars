import unrestricted.grammar


section functions_lift_sink

variables {T N₀ N : Type}

def lift_symbol_ (lift_N : N₀ → N) : symbol T N₀ → symbol T N
| (symbol.terminal ter) := symbol.terminal ter
| (symbol.nonterminal nonter) := symbol.nonterminal (lift_N nonter)

def sink_symbol_ (sink_N : N → option N₀) : symbol T N → option (symbol T N₀)
| (symbol.terminal ter) := some (symbol.terminal ter)
| (symbol.nonterminal nonter) := option.map symbol.nonterminal (sink_N nonter)

def lift_string_ (lift_N : N₀ → N) : list (symbol T N₀) → list (symbol T N) :=
list.map (lift_symbol_ lift_N)

def sink_string_ (sink_N : N → option N₀) : list (symbol T N) → list (symbol T N₀) :=
list.filter_map (sink_symbol_ sink_N)

def lift_rule_ (lift_N : N₀ → N) : grule T N₀ → grule T N :=
λ r : grule T N₀,
  ⟨ (lift_string_ lift_N r.input_string.first, lift_N r.input_string.secon, lift_string_ lift_N r.input_string.third),
    lift_string_ lift_N r.output_string ⟩

end functions_lift_sink


section lifting_conditions

structure lifted_grammar_ (T : Type) :=
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

private lemma lifted_grammar_inverse {T : Type} (lg : lifted_grammar_ T) :
  ∀ x : lg.g.nt,
    (∃ val, lg.sink_nt x = some val) →
      option.map lg.lift_nt (lg.sink_nt x) = x :=
begin
  intros x h,
  cases h with valu ass,
  rw ass,
  rw option.map_some',
  apply congr_arg,
  symmetry,
  by_contradiction,
  have inje := lg.sink_inj x (lg.lift_nt valu),
  rw lg.lift_nt_sink at inje,
  cases inje ass with case_valu case_none,
  {
    exact h case_valu,
  },
  rw ass at case_none,
  clear_except case_none,
  tauto,
end

end lifting_conditions


section translating_derivations

variables {T : Type} {lg : lifted_grammar_ T}

def good_letter_ : symbol T lg.g.nt → Prop
| (symbol.terminal t)     := true
| (symbol.nonterminal nt) := ∃ n₀ : lg.g₀.nt, lg.sink_nt nt = n₀

def good_string_ (str : list (symbol T lg.g.nt)) :=
∀ letter ∈ str, good_letter_ letter

-- TODO `lift_tran_`

lemma lift_deri_
    {input output : list (symbol T lg.g₀.nt)}
    (hyp : grammar_derives lg.g₀ input output) :
  grammar_derives lg.g (lift_string_ lg.lift_nt input) (lift_string_ lg.lift_nt output) :=
begin
  sorry,
end

-- TODO `sink_tran_`

lemma sink_deri_
    {input output : list (symbol T lg.g.nt)}
    (hyp : grammar_derives lg.g input output)
    (ok_input : good_string_ input) :
  grammar_derives lg.g₀ (sink_string_ lg.sink_nt input) (sink_string_ lg.sink_nt output)
  ∧ good_string_ output :=
begin
  sorry,
end

end translating_derivations
