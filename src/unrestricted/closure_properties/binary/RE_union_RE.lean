import unrestricted.grammarLiftSink


variables {T : Type}

private def union_grammar (g₁ g₂ : grammar T) : grammar T :=
grammar.mk (option (g₁.nt ⊕ g₂.nt)) none (
  ⟨ ([], none, []), [symbol.nonterminal (some (sum.inl (g₁.initial)))] ⟩ ::
  ⟨ ([], none, []), [symbol.nonterminal (some (sum.inr (g₂.initial)))] ⟩ ::
  ((list.map (lift_rule_ (some ∘ sum.inl)) g₁.rules) ++
   (list.map (lift_rule_ (some ∘ sum.inr)) g₂.rules)
))


section auxiliary
variables {g₁ g₂ : grammar T}

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (option g₁.nt)
| none               := none
| (some (sum.inl n)) := some n
| (some (sum.inr _)) := none

private def oN₂_of_N : (union_grammar g₁ g₂).nt → (option g₂.nt)
| none               := none
| (some (sum.inl _)) := none
| (some (sum.inr n)) := some n


private def lg₁ : lifted_grammar_ T :=
lifted_grammar_.mk g₁ (union_grammar g₁ g₂) (option.some ∘ sum.inl) sorry sorry sorry oN₁_of_N sorry sorry

private def lg₂ : lifted_grammar_ T :=
lifted_grammar_.mk g₂ (union_grammar g₁ g₂) (option.some ∘ sum.inr) sorry sorry sorry oN₂_of_N sorry sorry


private lemma in_L₁_or_L₂_of_in_union {w : list T} (h : w ∈ grammar_language (union_grammar g₁ g₂)) :
  w ∈ grammar_language g₁  ∨  w ∈ grammar_language g₂  :=
begin
  sorry,
end


private lemma in_union_of_in_L₁ {w : list T} (h : w ∈ grammar_language g₁) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
begin
  unfold grammar_language at h ⊢,
  rw set.mem_set_of_eq at h ⊢,
  unfold grammar_generates at h ⊢,
  --change grammar_derives _ _ (list.map symbol.terminal w),
  --change grammar_derives _ _ (list.map symbol.terminal w) at h,
  apply grammar_deri_of_tran_deri,
  {
    use ⟨ ([], none, []), [symbol.nonterminal (some (sum.inl (g₁.initial)))] ⟩,
    split,
    {
      apply list.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  simp,
  --change grammar_derives lg₁.g₀ [symbol.nonterminal lg₁.g₀.initial] (list.map symbol.terminal w) at h,
  --convert_to (sink_deri_ h sorry).1,
  sorry,
end

private lemma in_union_of_in_L₂ {w : list T} (h : w ∈ grammar_language g₂) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
begin
  sorry,
end

end auxiliary


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
    exact in_L₁_or_L₂_of_in_union ass,
  },
  {
    intros w ass,
    cases ass with case₁ case₂,
    {
      rw ← h₁ at case₁,
      exact in_union_of_in_L₁ case₁,
    },
    {
      rw ← h₂ at case₂,
      exact in_union_of_in_L₂ case₂,
    },
  },
end
