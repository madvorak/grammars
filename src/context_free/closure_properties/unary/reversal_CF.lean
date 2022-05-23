import context_free.cfg

variable {T : Type}

def reverse_language (L : language T) : language T :=
λ w : list T, w.reverse ∈ L


section auxiliary

private def reversal_grammar (g : CF_grammar T) : CF_grammar T :=
CF_grammar.mk g.nt g.initial (list.map (
    λ r : g.nt × list (symbol T g.nt), (r.fst, list.reverse r.snd)
  ) g.rules)

private lemma dual_of_reversal_grammar (g : CF_grammar T) :
  reversal_grammar (reversal_grammar g) = g :=
begin
  cases g,
  unfold reversal_grammar,
  rw list.map_map,
  simp,
  dsimp,
  convert list.map_id, swap, exact T,
  simp,
  convert_to list.map ((λ (r : g_nt × list (symbol T g_nt)), (r.fst, r.snd.reverse.reverse))) g_rules = g_rules,
  convert_to list.map ((λ (r : g_nt × list (symbol T g_nt)), (r.fst, r.snd))) g_rules = g_rules;
  finish,
end

private lemma reversed_word_in_original_language
    {g : CF_grammar T}
    {w : list T}
    (hyp : w ∈ CF_language (reversal_grammar g)) :
  w.reverse ∈ CF_language g :=
begin
  unfold CF_language at *,
  rw set.mem_set_of_eq at *,
  unfold CF_generates at *,
  unfold CF_generates_str at *,
  have bude_indukce :
    ∀ v : list (symbol T g.nt),
      CF_derives (reversal_grammar g) [symbol.nonterminal (reversal_grammar g).initial] v →
        CF_derives g [symbol.nonterminal g.initial] v.reverse,
  {
    intros v hv,
    unfold CF_derives at *,
    induction hv,
    {
      rw list.reverse_singleton,
      sorry,
    },
    sorry,
  },
  have instantse := bude_indukce (list.map symbol.terminal w),
  rw ← list.map_reverse at instantse,
  exact instantse hyp,
end

end auxiliary


/-- The class of context-free languages is closed under reversal. -/
theorem CF_of_reverse_CF (L : language T) :
  is_CF L  →  is_CF (reverse_language L)  :=
begin
  rintro ⟨ g, hgL ⟩,
  use reversal_grammar g,
  apply set.eq_of_subset_of_subset,
  {
    intros w hwL,
    unfold reverse_language,
    change w.reverse ∈ L,
    rw ← hgL,

    exact reversed_word_in_original_language hwL,
  },
  {
    intros w hwL,
    unfold reverse_language at hwL,
    change w.reverse ∈ L at hwL,
    rw ← hgL at hwL,

    have pre_reversal : ∃ g₀, g = reversal_grammar g₀,
    {
      use reversal_grammar g,
      rw dual_of_reversal_grammar,
    },
    cases pre_reversal with g₀ pre_rev,
    rw pre_rev at hwL ⊢,
    have finished_modulo_reverses := reversed_word_in_original_language hwL,
    rw dual_of_reversal_grammar,
    rw list.reverse_reverse at finished_modulo_reverses,
    exact finished_modulo_reverses,
  },
end
