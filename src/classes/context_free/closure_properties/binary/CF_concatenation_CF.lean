import classes.context_free.cfg
import classes.unrestricted.closure_properties.binary.RE_concatenation_RE


variables {T : Type}

private def wrap_CF_rule₁ {N₁ : Type} (N₂ : Type) (r : (N₁ × list (symbol T N₁))) :
  ((nnn T N₁ N₂) × list (nst T N₁ N₂)) :=
((sum.inl (some (sum.inl r.fst))), (list.map (wrap_symbol₁ N₂) r.snd))

private def wrap_CF_rule₂ {N₂ : Type} (N₁ : Type) (r : (N₂ × list (symbol T N₂))) :
  ((nnn T N₁ N₂) × list (nst T N₁ N₂)) :=
((sum.inl (some (sum.inr r.fst))), (list.map (wrap_symbol₂ N₁) r.snd))

private def CF_rules_for_terminals₁ (N₂ : Type) (g : CF_grammar T) :
  list ((nnn T g.nt N₂) × list (nst T g.nt N₂)) :=
list.map (λ t, ((sum.inr (sum.inl t)), [symbol.terminal t])) (all_used_terminals (grammar_of_cfg g))

private def CF_rules_for_terminals₂ (N₁ : Type) (g : CF_grammar T) :
  list ((nnn T N₁ g.nt) × list (nst T N₁ g.nt)) :=
list.map (λ t, ((sum.inr (sum.inr t)), [symbol.terminal t])) (all_used_terminals (grammar_of_cfg g))

private def big_CF_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk
  (nnn T g₁.nt g₂.nt)
  (sum.inl none)
  (((sum.inl none), [
    symbol.nonterminal (sum.inl (some (sum.inl g₁.initial))),
    symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]
  ) :: (
    (list.map (wrap_CF_rule₁ g₂.nt) g₁.rules ++ list.map (wrap_CF_rule₂ g₁.nt) g₂.rules) ++
    (CF_rules_for_terminals₁ g₂.nt g₁ ++ CF_rules_for_terminals₂ g₁.nt g₂)
  ))

private lemma big_CF_grammar_same_language (g₁ g₂ : CF_grammar T) :
  CF_language (big_CF_grammar g₁ g₂) = grammar_language (big_grammar (grammar_of_cfg g₁) (grammar_of_cfg g₂)) :=
begin
  rw CF_language_eq_grammar_language,
  congr,
  unfold big_CF_grammar,
  unfold grammar_of_cfg,
  unfold big_grammar,
  dsimp only [list.map],
  congr,
  repeat {
    rw list.map_append,
  },
  trim,
  {
    apply congr_arg2,
    {
      unfold rules_for_terminals₁,
      unfold CF_rules_for_terminals₁,
      finish,
    },
    {
      unfold rules_for_terminals₂,
      unfold CF_rules_for_terminals₂,
      finish,
    },
  },
end


/-- The class of context-free languages is closed under concatenation. -/
theorem CF_of_CF_c_CF (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ * L₂)   :=
begin
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩,
  rw CF_language_eq_grammar_language g₁ at eq_L₁,
  rw CF_language_eq_grammar_language g₂ at eq_L₂,

  use big_CF_grammar g₁ g₂,
  rw big_CF_grammar_same_language,

  apply set.eq_of_subset_of_subset,
  {
    intros w hyp,
    rw [←eq_L₁, ←eq_L₂],
    exact in_concatenated_of_in_big hyp,
  },
  {
    intros w hyp,
    rw [←eq_L₁, ←eq_L₂] at hyp,
    exact in_big_of_in_concatenated hyp,
  },
end
