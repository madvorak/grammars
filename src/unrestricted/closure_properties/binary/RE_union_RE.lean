import unrestricted.grammarLiftSink


variables {T : Type} (g₁ g₂ : grammar T)

private def union_grammar : grammar T :=
grammar.mk (option (g₁.nt ⊕ g₂.nt)) none (
  ⟨ ([], none, []), [symbol.nonterminal (some (sum.inl (g₁.initial)))] ⟩  ::
  ⟨ ([], none, []), [symbol.nonterminal (some (sum.inr (g₂.initial)))] ⟩  ::
  ((list.map (lift_rule_ (some ∘ sum.inl)) g₁.rules) ++
   (list.map (lift_rule_ (some ∘ sum.inr)) g₂.rules)
))


private def lg₁ : lifted_grammar_ T :=
lifted_grammar_.mk g₁ (union_grammar g₁ g₂) (some ∘ sum.inl) sorry sorry sorry sorry sorry sorry

private def lg₂ : lifted_grammar_ T :=
lifted_grammar_.mk g₂ (union_grammar g₁ g₂) (some ∘ sum.inr) sorry sorry sorry sorry sorry sorry


private lemma in_language_of_in_union (w : list T) :
  w ∈ grammar_language (union_grammar g₁ g₂)  →
    w ∈ grammar_language g₁  ∨  w ∈ grammar_language g₂  :=
begin
  sorry,
end


private lemma in_union_of_in_L₁ (w : list T) :
  w ∈ grammar_language g₁ → w ∈ grammar_language (union_grammar g₁ g₂) :=
begin
  sorry,
end

private lemma in_union_of_in_L₂ (w : list T) :
  w ∈ grammar_language g₂ → w ∈ grammar_language (union_grammar g₁ g₂) :=
begin
  sorry,
end


/-- The class of recursively-enumerable languages is closed under union. -/
theorem RE_of_RE_u_RE (L₁ : language T) (L₂ : language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ + L₂)   :=
begin
  rintro ⟨ ⟨ g₁, h₁ ⟩, ⟨ g₂, h₂ ⟩ ⟩,

  unfold is_RE,
  use union_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    intros w ass,
    rw language.mem_add,
    rw ← h₁,
    rw ← h₂,
    exact in_language_of_in_union g₁ g₂ w ass,
  },
  {
    intros w ass,
    cases ass with case₁ case₂,
    {
      rw ← h₁ at case₁,
      exact in_union_of_in_L₁ g₁ g₂ w case₁,
    },
    {
      rw ← h₂ at case₂,
      exact in_union_of_in_L₂ g₁ g₂ w case₂,
    },
  },
end
