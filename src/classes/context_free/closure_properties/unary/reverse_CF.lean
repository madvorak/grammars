import classes.context_free.cfg
import utilities.language_operations


variables {T : Type}

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
  dsimp only,
  rw list.map_map,
  simp only [eq_self_iff_true, heq_iff_eq, true_and],
  change list.map ((
      λ (r : g_nt × list (symbol T g_nt)), (r.fst, r.snd.reverse)) ∘
      λ (r : g_nt × list (symbol T g_nt)), (r.fst, r.snd.reverse))
     g_rules = g_rules,
  convert_to list.map ((λ (r : g_nt × list (symbol T g_nt)), (r.fst, r.snd.reverse.reverse))) g_rules = g_rules,
  convert_to list.map ((λ (r : g_nt × list (symbol T g_nt)), (r.fst, r.snd))) g_rules = g_rules,
  {
    simp [list.reverse_reverse],
  },
  {
    simp,
  },
end

private lemma derives_reversed (g : CF_grammar T) (v : list (symbol T g.nt)) :
  CF_derives (reversal_grammar g) [symbol.nonterminal (reversal_grammar g).initial] v →
    CF_derives g [symbol.nonterminal g.initial] v.reverse :=
begin
  intro hv,
  induction hv with u w trash orig ih,
  {
    rw list.reverse_singleton,
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran ih,
  rcases orig with ⟨r, rin, x, y, bef, aft⟩,
  change r ∈ (list.map (
      λ r : g.nt × list (symbol T g.nt), (r.fst, list.reverse r.snd)
    ) g.rules) at rin,
  rw list.mem_map at rin,
  rcases rin with ⟨r₀, rin₀, r_from_r₀⟩,
  use r₀,
  split,
  {
    exact rin₀,
  },
  use y.reverse,
  use x.reverse,
  split,
  {
    rw ←list.reverse_singleton,
    rw ←list.reverse_append_append,
    have fst_from_r : r₀.fst = r.fst,
    {
      rw ←r_from_r₀,
    },
    rw fst_from_r,
    exact congr_arg list.reverse bef,
  },
  {
    have snd_from_r : r₀.snd = r.snd.reverse,
    {
      rw ←r_from_r₀,
      rw list.reverse_reverse,
    },
    rw snd_from_r,
    rw ←list.reverse_append_append,
    exact congr_arg list.reverse aft,
  },
end

private lemma reversed_word_in_original_language {g : CF_grammar T} {w : list T}
    (hyp : w ∈ CF_language (reversal_grammar g)) :
  w.reverse ∈ CF_language g :=
begin
  unfold CF_language at *,
  rw set.mem_set_of_eq at *,
  unfold CF_generates at *,
  unfold CF_generates_str at *,
  rw list.map_reverse,
  exact derives_reversed g (list.map symbol.terminal w) hyp,
end

end auxiliary


/-- The class of context-free languages is closed under reversal. -/
theorem CF_of_reverse_CF (L : language T) :
  is_CF L  →  is_CF (reverse_lang L)  :=
begin
  rintro ⟨g, hgL⟩,
  rw ←hgL,

  use reversal_grammar g,
  unfold reverse_lang,

  apply set.eq_of_subset_of_subset,
  {
    intros w hwL,
    change w.reverse ∈ CF_language g,

    exact reversed_word_in_original_language hwL,
  },
  {
    intros w hwL,
    change w.reverse ∈ CF_language g at hwL,

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
