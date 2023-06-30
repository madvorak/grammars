import classes.context_sensitive.basics.toolbox
import classes.unrestricted.basics.toolbox

variables {T : Type}


def grammar_of_csg (g : CS_grammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map 
  (λ r : csrule T g.nt, grule.mk
    r.context_left r.input_nonterminal r.context_right
    (r.context_left ++ r.output_string ++ r.context_right)
  ) g.rules)

lemma CS_language_eq_grammar_language (g : CS_grammar T) :
  CS_language g = grammar_language (grammar_of_csg g) :=
begin
  unfold CS_language,
  unfold grammar_language,
  ext1 w,
  rw set.mem_set_of_eq,
  split,
  {
    have indu :
      ∀ v : list (symbol T g.nt),
        CS_derives g [symbol.nonterminal g.initial] v →
          grammar_derives (grammar_of_csg g) [symbol.nonterminal (grammar_of_csg g).initial] v,
    {
      clear w,
      intros v hypo,
      induction hypo with x y trash hyp ih,
      {
        apply grammar_deri_self,
      },
      apply grammar_deri_of_deri_tran,
      {
        exact ih,
      },
      unfold CS_transforms at hyp,
      unfold grammar_transforms,
      delta grammar_of_csg,
      dsimp only,
      rcases hyp with ⟨r, rin, u, w, bef, aft⟩,
      use grule.mk
        r.context_left r.input_nonterminal r.context_right
        (r.context_left ++ r.output_string ++ r.context_right),
      split,
      {
        rw list.mem_map,
        use r,
        split,
        {
          exact rin,
        },
        {
          refl,
        },
      },
      use u,
      use w,
      split,
      {
        exact bef,
      },
      simpa [list.append_assoc] using aft,
    },
    exact indu (list.map symbol.terminal w),
  },
  {
    have indu :
      ∀ v : list (symbol T g.nt),
        grammar_derives (grammar_of_csg g) [symbol.nonterminal (grammar_of_csg g).initial] v →
          CS_derives g [symbol.nonterminal g.initial] v,
    {
      clear w,
      intros v hypo,
      induction hypo with x y trash hyp ih,
      {
        apply CS_deri_self,
      },
      apply CS_deri_of_deri_tran,
      {
        exact ih,
      },
      unfold grammar_transforms at hyp,
      unfold CS_transforms,
      delta grammar_of_csg at hyp,
      dsimp only at hyp,
      rcases hyp with ⟨r, rin, u, w, bef, aft⟩,
      rw list.mem_map at rin,
      rcases rin with ⟨r', new_rule_in, new_rule_def⟩,
      use r',
      split,
      {
        exact new_rule_in,
      },
      use u,
      use w,
      split,
      {
        rw ←new_rule_def at bef,
        exact bef,
      },
      {
        rw ←new_rule_def at aft,
        simpa [list.append_assoc] using aft,
      },
    },
    exact indu (list.map symbol.terminal w),
  },
end

theorem CS_subclass_RE {L : language T} :
  is_CS L → is_RE L :=
begin
  rintro ⟨g, eq_L⟩,
  use grammar_of_csg g,
  rw ←eq_L,
  rw CS_language_eq_grammar_language,
end
