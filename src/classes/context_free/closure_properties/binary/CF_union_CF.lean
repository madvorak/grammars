import classes.context_free.cfg
import classes.unrestricted.closure_properties.binary.RE_union_RE


variables {T : Type}

private def lift_CF_rule₁ {N₁ : Type} (N₂ : Type) (r : (N₁ × list (symbol T N₁))) :
  (option (N₁ ⊕ N₂)) × list (symbol T (option (N₁ ⊕ N₂))) :=
(some (sum.inl r.fst), lift_string (option.some ∘ sum.inl) r.snd)

private def lift_CF_rule₂ (N₁ : Type) {N₂ : Type} (r : (N₂ × list (symbol T N₂))) :
  (option (N₁ ⊕ N₂)) × list (symbol T (option (N₁ ⊕ N₂))) :=
(some (sum.inr r.fst), lift_string (option.some ∘ sum.inr) r.snd)

private def union_CF_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (option (g₁.nt ⊕ g₂.nt)) none (
  (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) :: (
  (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) :: (
  (list.map (lift_CF_rule₁ g₂.nt) g₁.rules) ++
  (list.map (lift_CF_rule₂ g₁.nt) g₂.rules))))

private lemma union_grammar_eq_union_CF_grammar {g₁ g₂ : CF_grammar T} :
  union_grammar (grammar_of_cfg g₁) (grammar_of_cfg g₂)  =  grammar_of_cfg (union_CF_grammar g₁ g₂)  :=
begin
  unfold union_CF_grammar grammar_of_cfg union_grammar,
  dsimp only [list.map],
  congr,
  rw list.map_append,
  finish,
end

private lemma union_CF_grammar_same_language (g₁ g₂ : CF_grammar T) :
  CF_language (union_CF_grammar g₁ g₂)  =  grammar_language (union_grammar (grammar_of_cfg g₁) (grammar_of_cfg g₂))  :=
begin
  rw CF_language_eq_grammar_language,
  rw union_grammar_eq_union_CF_grammar,
end

/-- The class of context-free languages is closed under union. -/
theorem CF_of_CF_u_CF (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ + L₂)   :=
begin
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩,
  rw CF_language_eq_grammar_language g₁ at eq_L₁,
  rw CF_language_eq_grammar_language g₂ at eq_L₂,

  use union_CF_grammar g₁ g₂,
  rw union_CF_grammar_same_language,

  apply set.eq_of_subset_of_subset,
  {
    intros w hyp,
    rw [←eq_L₁, ←eq_L₂],
    exact in_L₁_or_L₂_of_in_union hyp,
  },
  {
    intros w hyp,
    cases hyp with case_1 case_2,
    {
      rw ←eq_L₁ at case_1,
      exact in_union_of_in_L₁ case_1,
    },
    {
      rw ←eq_L₂ at case_2,
      exact in_union_of_in_L₂ case_2,
    },
  },
end
