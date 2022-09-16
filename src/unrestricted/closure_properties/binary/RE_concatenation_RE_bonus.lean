import context_free.cfg
import unrestricted.closure_properties.binary.RE_concatenation_RE


variables {T : Type}

section bonus_CF

private def wrap_CF_rule₁ {N₁ : Type} (N₂ : Type) (r : (N₁ × list (symbol T N₁))) :
  ((@nnn T N₁ N₂) × list (symbol T (@nnn T N₁ N₂))) :=
((sum.inl (some (sum.inl r.fst))), (list.map (wrap_symbol₁ N₂) r.snd))

private def wrap_CF_rule₂ {N₂ : Type} (N₁ : Type) (r : (N₂ × list (symbol T N₂))) :
  ((@nnn T N₁ N₂) × list (symbol T (@nnn T N₁ N₂))) :=
((sum.inl (some (sum.inr r.fst))), (list.map (wrap_symbol₂ N₁) r.snd))

private def CF_rules_for_terminals₁ (N₂ : Type) (g : CF_grammar T) :
  list ((@nnn T g.nt N₂) × list (symbol T (@nnn T g.nt N₂))) :=
list.map (λ t, ((sum.inr (sum.inl t)), [symbol.terminal t])) (all_used_terminals (grammar_of_cfg g))

private def CF_rules_for_terminals₂ (N₁ : Type) (g : CF_grammar T) :
  list ((@nnn T N₁ g.nt) × list (symbol T (@nnn T N₁ g.nt))) :=
list.map (λ t, ((sum.inr (sum.inr t)), [symbol.terminal t])) (all_used_terminals (grammar_of_cfg g))

private def big_CF_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk
  (nnn g₁.nt g₂.nt)
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
  dsimp,
  congr,
  repeat {
    rw list.map_append,
  },
  apply congr_arg2,
  {
    apply congr_arg2;
    finish,
  },
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

/-- The class of context-free languages is closed under concatenation.
    This theorem is proved by translation from general grammars.
    Compare to `context_free.closure_properties.binary.CF_concatenation_CF.lean` which uses
    a simpler and more effective construction (based on context-gree grammars only). -/
private theorem bonus_CF_of_CF_c_CF (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ * L₂)   :=
begin
  rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩,
  rw CF_language_eq_grammar_language g₁ at h₁,
  rw CF_language_eq_grammar_language g₂ at h₂,

  use big_CF_grammar g₁ g₂,
  rw big_CF_grammar_same_language,

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

end bonus_CF


section bonus_CS

private def wrap_CS_rule₁ {N₁ : Type} (N₂ : Type) (r : csrule T N₁) :
  csrule T (@nnn T N₁ N₂) :=
csrule.mk
  (list.map (wrap_symbol₁ N₂) r.context_left)
  (sum.inl (some (sum.inl r.input_nonterminal)))
  (list.map (wrap_symbol₁ N₂) r.context_right)
  (list.map (wrap_symbol₁ N₂) r.output_string)

private def wrap_CS_rule₂ {N₂ : Type} (N₁ : Type) (r : csrule T N₂) :
  csrule T (@nnn T N₁ N₂) :=
csrule.mk
  (list.map (wrap_symbol₂ N₁) r.context_left)
  (sum.inl (some (sum.inr r.input_nonterminal)))
  (list.map (wrap_symbol₂ N₁) r.context_right)
  (list.map (wrap_symbol₂ N₁) r.output_string)

private def CS_rules_for_terminals₁ (N₂ : Type) (g : CS_grammar T) :
  list (csrule T (@nnn T g.nt N₂)) :=
list.map (λ t, csrule.mk [] (sum.inr (sum.inl t)) [] [symbol.terminal t]) (all_used_terminals (grammar_of_csg g))

private def CS_rules_for_terminals₂ (N₁ : Type) (g : CS_grammar T) :
  list (csrule T (@nnn T N₁ g.nt)) :=
list.map (λ t, csrule.mk [] (sum.inr (sum.inr t)) [] [symbol.terminal t]) (all_used_terminals (grammar_of_csg g))

private def big_CS_grammar (g₁ g₂ : CS_grammar T) : CS_grammar T :=
CS_grammar.mk
  (nnn g₁.nt g₂.nt)
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
  dsimp,
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

end bonus_CS


#check        RE_of_RE_c_RE
#print axioms RE_of_RE_c_RE

#check        bonus_CF_of_CF_c_CF
#print axioms bonus_CF_of_CF_c_CF

#check        bonus_CS_of_CS_c_CS
#print axioms bonus_CS_of_CS_c_CS
