import unrestricted.grammar


section functions_lift_sink

variables {T N₀ N : Type}

def lift_symbol (lift_N : N₀ → N) : symbol T N₀ → symbol T N
| (symbol.terminal ter) := symbol.terminal ter
| (symbol.nonterminal nonter) := symbol.nonterminal (lift_N nonter)

def sink_symbol (sink_N : N → option N₀) : symbol T N → option (symbol T N₀)
| (symbol.terminal ter) := some (symbol.terminal ter)
| (symbol.nonterminal nonter) := option.map symbol.nonterminal (sink_N nonter)

def lift_string (lift_N : N₀ → N) : list (symbol T N₀) → list (symbol T N) :=
list.map (lift_symbol lift_N)

def sink_string (sink_N : N → option N₀) : list (symbol T N) → list (symbol T N₀) :=
list.filter_map (sink_symbol sink_N)

def lift_rule (lift_N : N₀ → N) : grule T N₀ → grule T N :=
λ r : grule T N₀, grule.mk
  (lift_string lift_N r.input_L)
  (lift_N r.input_N)
  (lift_string lift_N r.input_R)
  (lift_string lift_N r.output_string)

end functions_lift_sink


section lifting_conditions

structure lifted_grammar (T : Type) :=
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
    lift_rule lift_nt r ∈ g.rules
)
(preimage_of_rules : ∀ r : grule T g.nt,
  (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, lift_nt n₀ = r.input_N) →
    (∃ r₀ ∈ g₀.rules, lift_rule lift_nt r₀ = r)
)

private lemma lifted_grammar_inverse {T : Type} (lg : lifted_grammar T) :
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
  exact option.no_confusion case_none,
end

end lifting_conditions


section translating_derivations

variables {T : Type}

private lemma lift_tran {lg : lifted_grammar T} {w₁ w₂ : list (symbol T lg.g₀.nt)}
    (hyp : grammar_transforms lg.g₀ w₁ w₂) :
  grammar_transforms lg.g (lift_string lg.lift_nt w₁) (lift_string lg.lift_nt w₂) :=
begin
  rcases hyp with ⟨rule, rule_in, u, v, bef, aft⟩,
  use lift_rule lg.lift_nt rule,
  split,
  {
    exact lg.corresponding_rules rule rule_in,
  },
  use lift_string lg.lift_nt u,
  use lift_string lg.lift_nt v,
  split,
  {
    have lift_bef := congr_arg (lift_string lg.lift_nt) bef,
    unfold lift_string at *,
    rw list.map_append_append at lift_bef,
    rw list.map_append_append at lift_bef,
    exact lift_bef,
  },
  {
    have lift_aft := congr_arg (lift_string lg.lift_nt) aft,
    unfold lift_string at *,
    rw list.map_append_append at lift_aft,
    exact lift_aft,
  },
end

lemma lift_deri (lg : lifted_grammar T) {w₁ w₂ : list (symbol T lg.g₀.nt)}
    (hyp : grammar_derives lg.g₀ w₁ w₂) :
  grammar_derives lg.g (lift_string lg.lift_nt w₁) (lift_string lg.lift_nt w₂) :=
begin
  induction hyp with u v trash orig ih,
  {
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran,
  {
    exact ih,
  },
  exact lift_tran orig,
end


def good_letter {lg : lifted_grammar T} : symbol T lg.g.nt → Prop
| (symbol.terminal t)     := true
| (symbol.nonterminal nt) := ∃ n₀ : lg.g₀.nt, lg.sink_nt nt = n₀

def good_string {lg : lifted_grammar T} (s : list (symbol T lg.g.nt)) :=
∀ letter ∈ s, good_letter letter

private lemma sink_tran {lg : lifted_grammar T} {w₁ w₂ : list (symbol T lg.g.nt)}
    (hyp : grammar_transforms lg.g w₁ w₂)
    (ok_input : good_string w₁) :
  grammar_transforms lg.g₀ (sink_string lg.sink_nt w₁) (sink_string lg.sink_nt w₂)
  ∧ good_string w₂ :=
begin
  rcases hyp with ⟨rule, rule_in, u, v, bef, aft⟩,

  rcases lg.preimage_of_rules rule (by {
    split,
    {
      exact rule_in,
    },
    rw bef at ok_input,
    have good_matched_nonterminal : good_letter (symbol.nonterminal rule.input_N),
    {
      apply ok_input (symbol.nonterminal rule.input_N),
      apply list.mem_append_left,
      apply list.mem_append_left,
      apply list.mem_append_right,
      rw list.mem_singleton,
    },
    change ∃ n₀ : lg.g₀.nt, lg.sink_nt rule.input_N = some n₀ at good_matched_nonterminal,
    cases good_matched_nonterminal with n₀ hn₀,
    use n₀,
    have almost := congr_arg (option.map lg.lift_nt) hn₀,
    rw lifted_grammar_inverse lg rule.input_N ⟨n₀, hn₀⟩ at almost,
    rw option.map_some' at almost,
    apply option.some_injective,
    exact almost.symm,
  }) with ⟨pre_rule, pre_in, preimage⟩,

  split, swap,
  {
    rw bef at ok_input,
    rw aft,
    unfold good_string at ok_input ⊢,
    rw ←preimage,
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
      unfold good_letter,
    },
    unfold lift_rule at a_in_ros,
    dsimp only at a_in_ros,
    unfold lift_string at a_in_ros,
    rw list.mem_map at a_in_ros,
    rcases a_in_ros with ⟨s, trash, a_from_s⟩,
    rw ←a_from_s,
    cases s,
    {
      exfalso,
      clear_except a_from_s,
      unfold lift_symbol at a_from_s,
      exact symbol.no_confusion a_from_s,
    },
    unfold lift_symbol,
    unfold good_letter,
    use s,
    exact lg.lift_nt_sink s,
  },
  use pre_rule,
  split,
  {
    exact pre_in,
  },
  use sink_string lg.sink_nt u,
  use sink_string lg.sink_nt v,
  have correct_inverse : sink_symbol lg.sink_nt ∘ lift_symbol lg.lift_nt = option.some,
  {
    ext1,
    cases x,
    {
      refl,
    },
    rw function.comp_app,
    unfold lift_symbol,
    unfold sink_symbol,
    rw lg.lift_nt_sink,
    apply option.map_some',
  },
  split,
  {
    have sink_bef := congr_arg (sink_string lg.sink_nt) bef,
    unfold sink_string at *,
    rw list.filter_map_append_append at sink_bef,
    rw list.filter_map_append_append at sink_bef,
    convert sink_bef;
    rw ←preimage;
    unfold lift_rule;
    dsimp only;
    clear_except correct_inverse,
    {
      unfold lift_string,
      rw list.filter_map_map,
      rw correct_inverse,
      rw list.filter_map_some,
    },
    {
      change
        [symbol.nonterminal pre_rule.input_N] =
        list.filter_map (sink_symbol lg.sink_nt)
          (list.map (lift_symbol lg.lift_nt) [symbol.nonterminal pre_rule.input_N]),
      rw list.filter_map_map,
      rw correct_inverse,
      rw list.filter_map_some,
    },
    {
      unfold lift_string,
      rw list.filter_map_map,
      rw correct_inverse,
      rw list.filter_map_some,
    },
  },
  {
    have sink_aft := congr_arg (sink_string lg.sink_nt) aft,
    unfold sink_string at *,
    rw list.filter_map_append_append at sink_aft,
    convert sink_aft,
    rw ←preimage,
    clear_except correct_inverse,
    unfold lift_rule,
    dsimp only,
    unfold lift_string,
    rw list.filter_map_map,
    rw correct_inverse,
    rw list.filter_map_some,
  },
end

private lemma sink_deri_aux {lg : lifted_grammar T} {w₁ w₂ : list (symbol T lg.g.nt)}
    (hyp : grammar_derives lg.g w₁ w₂)
    (ok_input : good_string w₁) :
  grammar_derives lg.g₀ (sink_string lg.sink_nt w₁) (sink_string lg.sink_nt w₂)
  ∧ good_string w₂ :=
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
  have both := sink_tran orig ih.2,

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

lemma sink_deri (lg : lifted_grammar T) {w₁ w₂ : list (symbol T lg.g.nt)}
    (hyp : grammar_derives lg.g w₁ w₂)
    (ok_input : good_string w₁) :
  grammar_derives lg.g₀ (sink_string lg.sink_nt w₁) (sink_string lg.sink_nt w₂) :=
begin
  exact (sink_deri_aux hyp ok_input).1
end

end translating_derivations
