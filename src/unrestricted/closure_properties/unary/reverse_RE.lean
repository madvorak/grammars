import context_free.closure_properties.unary.reverse_CF

variable {T : Type}


section auxiliary

private def reversal_grammar (g : grammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map (
    λ r : grule T g.nt,
      ⟨ (r.input_string.snd.snd.reverse, r.input_string.snd.fst, r.input_string.fst.reverse), r.output_string.reverse ⟩
  ) g.rules)

private lemma dual_of_reversal_grammar (g : grammar T) :
  reversal_grammar (reversal_grammar g) = g :=
begin
  unfold reversal_grammar,
  --simp [ list.map_map, list.reverse_reverse, list.map_id ],
  sorry,
end

private lemma derives_reversed (g : grammar T) (v : list (symbol T g.nt)) :
  grammar_derives (reversal_grammar g) [symbol.nonterminal (reversal_grammar g).initial] v →
    grammar_derives g [symbol.nonterminal g.initial] v.reverse :=
begin
  intro hv,
  induction hv with u w trash orig ih,
  {
    rw list.reverse_singleton,
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran ih,
  rcases orig with ⟨ r, rin, x, y, bef, aft ⟩,
  change r ∈ (list.map _ g.rules) at rin,
  rw list.mem_map at rin,
  rcases rin with ⟨ r₀, rin₀, r_from_r₀ ⟩,
  use r₀,
  split,
  {
    exact rin₀,
  },
  use y.reverse,
  use x.reverse,
  split,
  {
    have rid₁ : r₀.input_string.fst = r.input_string.snd.snd.reverse,
    {
      rw ← r_from_r₀,
      rw list.reverse_reverse,
    },
    have rid₂ : [symbol.nonterminal r₀.input_string.snd.fst] = [symbol.nonterminal r.input_string.snd.fst].reverse,
    {
      rw ← r_from_r₀,
      rw list.reverse_singleton,
    },
    have rid₃ : r₀.input_string.snd.snd = r.input_string.fst.reverse,
    {
      rw ← r_from_r₀,
      rw list.reverse_reverse,
    },
    rw [ rid₁, rid₂, rid₃,
         ← list_reverse_append_append, ← list_reverse_append_append,
         ← list.append_assoc, ← list.append_assoc ],
    congr,
    exact bef,
  },
  {
    have snd_from_r : r₀.output_string = r.output_string.reverse,
    {
      rw ← r_from_r₀,
      rw list.reverse_reverse,
    },
    rw snd_from_r,
    rw ← list_reverse_append_append,
    exact congr_arg list.reverse aft,
  },
end

private lemma reversed_word_in_original_language
    {g : grammar T}
    {w : list T}
    (hyp : w ∈ grammar_language (reversal_grammar g)) :
  w.reverse ∈ grammar_language g :=
begin
  unfold grammar_language at *,
  have almost_done := derives_reversed g (list.map symbol.terminal w) hyp,
  rw ← list.map_reverse at almost_done,
  exact almost_done,
end

end auxiliary


/-- The class of context-free languages is closed under reversal. -/
theorem RE_of_reverse_RE (L : language T) :
  is_Enumerable L  →  is_Enumerable (reverse_language L)  :=
begin
  rintro ⟨ g, hgL ⟩,
  rw ← hgL,

  use reversal_grammar g,
  unfold reverse_language,

  apply set.eq_of_subset_of_subset,
  {
    intros w hwL,
    change w.reverse ∈ grammar_language g,

    exact reversed_word_in_original_language hwL,
  },
  {
    intros w hwL,
    change w.reverse ∈ grammar_language g at hwL,

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
