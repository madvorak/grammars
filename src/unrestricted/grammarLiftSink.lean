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
  ⟨(lift_string_ lift_N r.input_string.first, lift_N r.input_string.secon, lift_string_ lift_N r.input_string.third),
    lift_string_ lift_N r.output_string⟩

end functions_lift_sink


section lifting_conditions

structure lifted_grammar_ (T : Type) :=
(g₀ g : grammar T)
(lift_nt : g₀.nt → g.nt)
(sink_nt : g.nt → option g₀.nt)
(lift_inj : function.injective lift_nt)
(sink_inj : ∀ x y, sink_nt x = sink_nt y →
  x = y  ∨  sink_nt x = none
)
(lift_nt_sink : ∀ n₀ : g₀.nt, sink_nt (lift_nt n₀) = some n₀)
(corresponding_rules : ∀ r : grule T g₀.nt,
  r ∈ g₀.rules →
    lift_rule_ lift_nt r ∈ g.rules
)
(preimage_of_rules : ∀ r : grule T g.nt,
  (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, lift_nt n₀ = r.input_string.secon) →
    (∃ r₀ ∈ g₀.rules, lift_rule_ lift_nt r₀ = r)
)

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

variables {T : Type}

private lemma lift_tran_
    {lg : lifted_grammar_ T}
    {input output : list (symbol T lg.g₀.nt)}
    (hyp : grammar_transforms lg.g₀ input output) :
  grammar_transforms lg.g (lift_string_ lg.lift_nt input) (lift_string_ lg.lift_nt output) :=
begin
  rcases hyp with ⟨rule, rule_in, v, w, bef, aft⟩,
  use lift_rule_ lg.lift_nt rule,
  split,
  {
    exact lg.corresponding_rules rule rule_in,
  },
  use lift_string_ lg.lift_nt v,
  use lift_string_ lg.lift_nt w,
  split,
  {
    have lift_bef := congr_arg (lift_string_ lg.lift_nt) bef,
    unfold lift_string_ at *,
    rw list.map_append_append at lift_bef,
    rw list.map_append_append at lift_bef,
    convert lift_bef,
  },
  {
    have lift_aft := congr_arg (lift_string_ lg.lift_nt) aft,
    unfold lift_string_ at *,
    rw list.map_append_append at lift_aft,
    exact lift_aft,
  },
end

lemma lift_deri_
    (lg : lifted_grammar_ T)
    {input output : list (symbol T lg.g₀.nt)}
    (hyp : grammar_derives lg.g₀ input output) :
  grammar_derives lg.g (lift_string_ lg.lift_nt input) (lift_string_ lg.lift_nt output) :=
begin
  induction hyp with u v trash orig ih,
  {
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran,
  {
    exact ih,
  },
  exact lift_tran_ orig,
end


def good_letter_ {lg : lifted_grammar_ T} : symbol T lg.g.nt → Prop
| (symbol.terminal t)     := true
| (symbol.nonterminal nt) := ∃ n₀ : lg.g₀.nt, lg.sink_nt nt = n₀

def good_string_ {lg : lifted_grammar_ T} (s : list (symbol T lg.g.nt)) :=
∀ letter ∈ s, good_letter_ letter

private lemma sink_tran_
    {lg : lifted_grammar_ T}
    {input output : list (symbol T lg.g.nt)}
    (hyp : grammar_transforms lg.g input output)
    (ok_input : good_string_ input) :
  grammar_transforms lg.g₀ (sink_string_ lg.sink_nt input) (sink_string_ lg.sink_nt output)
  ∧ good_string_ output :=
begin
  rcases hyp with ⟨rule, rule_in, v, w, bef, aft⟩,

  rcases lg.preimage_of_rules rule (by {
    split,
    {
      exact rule_in,
    },
    rw bef at ok_input,
    have good_matched_nonterminal : good_letter_ (symbol.nonterminal rule.input_string.secon),
    {
      apply ok_input (symbol.nonterminal rule.input_string.secon),
      apply list.mem_append_left,
      apply list.mem_append_left,
      apply list.mem_append_right,
      rw list.mem_singleton,
    },
    change ∃ n₀ : lg.g₀.nt, lg.sink_nt rule.input_string.secon = some n₀ at good_matched_nonterminal,
    cases good_matched_nonterminal with n₀ hn₀,
    use n₀,
    have almost := congr_arg (option.map lg.lift_nt) hn₀,
    rw lifted_grammar_inverse lg rule.input_string.secon ⟨n₀, hn₀⟩ at almost,
    simp at almost,
    apply option.some_injective,
    exact almost.symm,
  }) with ⟨pre_rule, pre_in, preimage⟩,

  split, swap,
  {
    rw bef at ok_input,
    rw aft,
    unfold good_string_ at ok_input ⊢,
    rw ← preimage,
    clear_except ok_input,
    rw list.forall_mem_append_append at ok_input ⊢,
    rw list.forall_mem_append_append at ok_input,
    split,
    {
      exact ok_input.1.1,
    },
    split, swap,
    {
      exact ok_input.2.2,
    },
    intros a a_in_ros,
    cases a,
    {
      clear_except,
      tauto,
    },
    unfold lift_rule_ at a_in_ros,
    dsimp at a_in_ros,
    unfold lift_string_ at a_in_ros,
    rw list.mem_map at a_in_ros,
    rcases a_in_ros with ⟨s, trash, a_from_s⟩,
    rw ← a_from_s,
    cases s,
    {
      exfalso,
      clear_except a_from_s,
      unfold lift_symbol_ at a_from_s,
      tauto,
    },
    unfold lift_symbol_,
    unfold good_letter_,
    use s,
    exact lg.lift_nt_sink s,
  },
  use pre_rule,
  split,
  {
    exact pre_in,
  },
  use sink_string_ lg.sink_nt v,
  use sink_string_ lg.sink_nt w,
  have correct_inverse : sink_symbol_ lg.sink_nt ∘ lift_symbol_ lg.lift_nt = option.some,
  {
    ext1,
    cases x,
    {
      refl,
    },
    dsimp,
    unfold lift_symbol_,
    unfold sink_symbol_,
    rw lg.lift_nt_sink,
    apply option.map_some',
  },
  split,
  {
    have sink_bef := congr_arg (sink_string_ lg.sink_nt) bef,
    unfold sink_string_ at *,
    rw list.filter_map_append_append at sink_bef,
    rw list.filter_map_append_append at sink_bef,
    convert sink_bef;
    rw ← preimage;
    unfold lift_rule_;
    dsimp;
    clear_except correct_inverse,
    {
      unfold lift_string_,
      unfold prod.first,
      rw list.filter_map_map,
      rw correct_inverse,
      rw list.filter_map_some,
    },
    {
      change
        [symbol.nonterminal pre_rule.input_string.secon] =
        list.filter_map (sink_symbol_ lg.sink_nt)
          (list.map (lift_symbol_ lg.lift_nt) [symbol.nonterminal pre_rule.input_string.secon]),
      rw list.filter_map_map,
      rw correct_inverse,
      rw list.filter_map_some,
    },
    {
      unfold lift_string_,
      unfold prod.third,
      rw list.filter_map_map,
      rw correct_inverse,
      rw list.filter_map_some,
    },
  },
  {
    have sink_aft := congr_arg (sink_string_ lg.sink_nt) aft,
    unfold sink_string_ at *,
    rw list.filter_map_append_append at sink_aft,
    convert sink_aft,
    rw ← preimage,
    clear_except correct_inverse,
    unfold lift_rule_,
    dsimp,
    unfold lift_string_,
    rw list.filter_map_map,
    rw correct_inverse,
    rw list.filter_map_some,
  },
end

private lemma sink_deri_aux
    {lg : lifted_grammar_ T}
    {input output : list (symbol T lg.g.nt)}
    (hyp : grammar_derives lg.g input output)
    (ok_input : good_string_ input) :
  grammar_derives lg.g₀ (sink_string_ lg.sink_nt input) (sink_string_ lg.sink_nt output)
  ∧ good_string_ output :=
begin
  induction hyp with u v trash orig ih,
  {
    split,
    {
      apply grammar_deri_self,
    },
    {
      exact ok_input,
    },
  },
  have both := sink_tran_ orig ih.2,

  split, swap,
  {
    exact both.2,
  },
  apply grammar_deri_of_deri_tran,
  {
    exact ih.1,
  },
  {
    exact both.1,
  },
end

lemma sink_deri_
    (lg : lifted_grammar_ T)
    {input output : list (symbol T lg.g.nt)}
    (hyp : grammar_derives lg.g input output)
    (ok_input : good_string_ input) :
  grammar_derives lg.g₀ (sink_string_ lg.sink_nt input) (sink_string_ lg.sink_nt output) :=
(sink_deri_aux hyp ok_input).1

end translating_derivations
