import classes.context_free.basics.toolbox
import classes.context_sensitive.basics.inclusion

variables {T : Type}


def csg_of_cfg (g : CF_grammar T) : CS_grammar T :=
CS_grammar.mk g.nt g.initial (list.map (λ r : g.nt × (list (symbol T g.nt)),
  csrule.mk [] r.fst [] r.snd) g.rules)

def grammar_of_cfg (g : CF_grammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map (λ r : g.nt × (list (symbol T g.nt)),
  grule.mk [] r.fst [] r.snd) g.rules)

lemma grammar_of_cfg_well_defined (g : CF_grammar T) :
  grammar_of_csg (csg_of_cfg g) = grammar_of_cfg g :=
begin
  unfold grammar_of_cfg,
  delta csg_of_cfg,
  delta grammar_of_csg,
  simp only [list.map_map, eq_self_iff_true, heq_iff_eq, true_and],
  ext1,
  rw [list.nth_map, list.nth_map],
  apply congr_fun,
  ext1,
  cases x,
  {
    refl,
  },
  apply congr_arg option.some,
  simp [list.append_nil],
end

lemma grammar_of_csg_of_cfg :
  grammar_of_csg ∘ csg_of_cfg = @grammar_of_cfg T :=
begin
  ext,
  apply grammar_of_cfg_well_defined,
end

lemma CF_language_eq_CS_language (g : CF_grammar T) :
  CF_language g = CS_language (csg_of_cfg g) :=
begin
  unfold CF_language,
  unfold CS_language,
  ext1 w,
  change
    CF_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w) =
    CS_derives (csg_of_cfg g) [symbol.nonterminal (csg_of_cfg g).initial] (list.map symbol.terminal w),
  rw eq_iff_iff,
  split,
  {
    have indu :
      ∀ v : list (symbol T g.nt),
        CF_derives g [symbol.nonterminal g.initial] v →
          CS_derives (csg_of_cfg g) [symbol.nonterminal (csg_of_cfg g).initial] v,
    {
      clear w,
      intros v h,
      induction h with x y trash hyp ih,
      {
        apply CS_deri_self,
      },
      apply CS_deri_of_deri_tran,
      {
        exact ih,
      },
      unfold CF_transforms at hyp,
      unfold CS_transforms,
      delta csg_of_cfg,
      dsimp only,
      rcases hyp with ⟨r, rin, u, w, bef, aft⟩,
      use csrule.mk [] r.fst [] r.snd,
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
      split;
      {
        dsimp only,
        rw list.append_nil,
        rw list.append_nil,
        assumption,
      },
    },
    exact indu (list.map symbol.terminal w),
  },
  {
    have indu :
      ∀ v : list (symbol T g.nt),
        CS_derives (csg_of_cfg g) [symbol.nonterminal g.initial] v →
          CF_derives g [symbol.nonterminal (csg_of_cfg g).initial] v,
    {
      clear w,
      intros v h,
      induction h with x y trash hyp ih,
      {
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran,
      {
        exact ih,
      },
      unfold CS_transforms at hyp,
      unfold CF_transforms,
      delta csg_of_cfg at hyp,
      dsimp only at hyp,
      rcases hyp with ⟨r, rin, u, w, bef, aft⟩,
      use (r.input_nonterminal, r.output_string),
      split,
      {
        finish,
      },
      use u,
      use w,
      have cl_empty : r.context_left = list.nil,
      {
        finish,
      },
      have cr_empty : r.context_right = list.nil,
      {
        finish,
      },
      rw [cl_empty, cr_empty] at *,
      repeat {
        rw list.append_nil at *,
      },
      split;
      assumption,
    },
    exact indu (list.map symbol.terminal w),
  },
end

lemma CF_language_eq_grammar_language (g : CF_grammar T) :
  CF_language g = grammar_language (grammar_of_cfg g) :=
begin
  rw ←grammar_of_cfg_well_defined,
  rw CF_language_eq_CS_language,
  rw CS_language_eq_grammar_language,
end

theorem CF_subclass_CS {L : language T} :
  is_CF L → is_CS L :=
begin
  rintro ⟨g, eq_L⟩,
  use csg_of_cfg g,
  rw ←eq_L,
  rw CF_language_eq_CS_language,
end

theorem CF_subclass_RE {L : language T} :
  is_CF L → is_RE L :=
CS_subclass_RE ∘ CF_subclass_CS
