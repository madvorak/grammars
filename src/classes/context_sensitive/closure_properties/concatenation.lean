import classes.context_sensitive.basics.inclusion
import classes.unrestricted.closure_properties.concatenation

variables {T : Type}


private def wrap_CS_rule₁ {N₁ : Type} (N₂ : Type) (r : csrule T N₁) :
  csrule T (nnn T N₁ N₂) :=
csrule.mk
  (list.map (wrap_symbol₁ N₂) r.context_left)
  (sum.inl (some (sum.inl r.input_nonterminal)))
  (list.map (wrap_symbol₁ N₂) r.context_right)
  (list.map (wrap_symbol₁ N₂) r.output_string)

private def wrap_CS_rule₂ {N₂ : Type} (N₁ : Type) (r : csrule T N₂) :
  csrule T (nnn T N₁ N₂) :=
csrule.mk
  (list.map (wrap_symbol₂ N₁) r.context_left)
  (sum.inl (some (sum.inr r.input_nonterminal)))
  (list.map (wrap_symbol₂ N₁) r.context_right)
  (list.map (wrap_symbol₂ N₁) r.output_string)

private def CS_rules_for_terminals₁ (N₂ : Type) (g : CS_grammar T) :
  list (csrule T (nnn T g.nt N₂)) :=
list.map (λ t, csrule.mk [] (sum.inr (sum.inl t)) [] [symbol.terminal t]) (all_used_terminals (grammar_of_csg g))

private def CS_rules_for_terminals₂ (N₁ : Type) (g : CS_grammar T) :
  list (csrule T (nnn T N₁ g.nt)) :=
list.map (λ t, csrule.mk [] (sum.inr (sum.inr t)) [] [symbol.terminal t]) (all_used_terminals (grammar_of_csg g))

private def big_CS_grammar (g₁ g₂ : CS_grammar T) : CS_grammar T :=
CS_grammar.mk
  (nnn T g₁.nt g₂.nt)
  (sum.inl none)
  ((csrule.mk [] (sum.inl none) [] [
    symbol.nonterminal (sum.inl (some (sum.inl g₁.initial))),
    symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]
  ) :: (
    (list.map (wrap_CS_rule₁ g₂.nt) g₁.rules ++ list.map (wrap_CS_rule₂ g₁.nt) g₂.rules) ++
    (CS_rules_for_terminals₁ g₂.nt g₁ ++ CS_rules_for_terminals₂ g₁.nt g₂)
  ))

private lemma big_CS_grammar_same_language (g₁ g₂ : CS_grammar T) :
  CS_language (big_CS_grammar g₁ g₂) = grammar_language (big_grammar (grammar_of_csg g₁) (grammar_of_csg g₂)) :=
begin
  rw CS_language_eq_grammar_language,
  congr,
  unfold big_CS_grammar,
  unfold grammar_of_csg,
  unfold big_grammar,
  dsimp only [list.map],
  congr,
  repeat {
    rw list.map_append,
  },
  apply congr_arg2,
  {
    apply congr_arg2;
    {
      rw list.map_map,
      rw list.map_map,
      apply congr_arg2,
      {
        ext,
        cases x,
        change _ = grule.mk _ _ _ _,
        finish,
      },
      refl,
    },
  },
  {
    apply congr_arg2,
    {
      unfold rules_for_terminals₁,
      unfold CS_rules_for_terminals₁,
      rw list.map_map,
      unfold grammar_of_csg,
      finish,
    },
    {
      unfold rules_for_terminals₂,
      unfold CS_rules_for_terminals₂,
      rw list.map_map,
      unfold grammar_of_csg,
      finish,
    },
  },
end

private theorem bonus_CS_of_CS_c_CS (L₁ : language T) (L₂ : language T) :
  is_CS L₁  ∧  is_CS L₂   →   is_CS (L₁ * L₂)   :=
begin
  rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩,
  rw CS_language_eq_grammar_language g₁ at h₁,
  rw CS_language_eq_grammar_language g₂ at h₂,

  use big_CS_grammar g₁ g₂,
  rw big_CS_grammar_same_language,

  apply set.eq_of_subset_of_subset,
  {
    intros w hyp,
    rw ←h₁,
    rw ←h₂,
    exact in_concatenated_of_in_big hyp,
  },
  {
    intros w hyp,
    rw ←h₁ at hyp,
    rw ←h₂ at hyp,
    exact in_big_of_in_concatenated hyp,
  },
end
