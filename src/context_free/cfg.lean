import context_sensitive.csg


section cfg_definitions

/-- Context-free grammar that generates words over the alphabet `termi` (a type of terminals). -/
structure CF_grammar (termi : Type) :=
(nt : Type)                                      -- type of nonterminals
(initial : nt)                                   -- initial symbol
(rules : list (nt × (list (symbol termi nt))))   -- rewriting rules


variables {T : Type} (g : CF_grammar T)

/-- One step of context-free transformation. -/
def CF_transforms (oldWord newWord : list (symbol T g.nt)) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbol T g.nt),
  oldWord = v ++ [symbol.nonterminal (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

/-- Any number of steps of context-free transformation; reflexive+transitive closure of `CF_transforms`. -/
def CF_derives : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CF_transforms g)

/-- Accepts a string (a list of symbols) iff it can be derived from the initial nonterminal. -/
def CF_generates_str (str : list (symbol T g.nt)) : Prop :=
CF_derives g [symbol.nonterminal g.initial] str

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def CF_generates (word : list T) : Prop :=
CF_generates_str g (list.map symbol.terminal word)

/-- Context-free language; just a wrapper around `CF_generates`. -/
def CF_language : language T :=
set_of (CF_generates g)

end cfg_definitions

/-- Predicate "is context-free"; defined by an existence of a context-free grammar for given language. -/
def is_CF {T : Type} (L : language T) : Prop :=
∃ g : CF_grammar T, CF_language g = L


section cfg_utilities
variables {T : Type} {g : CF_grammar T}

lemma CF_deri_of_tran {v w : list (symbol T g.nt)} :
  CF_transforms g v w → CF_derives g v w :=
relation.refl_trans_gen.single

/-- The relation `CF_derives` is reflexive. -/
lemma CF_deri_self {w : list (symbol T g.nt)} :
  CF_derives g w w :=
relation.refl_trans_gen.refl

/-- The relation `CF_derives` is transitive. -/
lemma CF_deri_of_deri_deri
    {u v w : list (symbol T g.nt)}
    (huv : CF_derives g u v)
    (hvw : CF_derives g v w) :
  CF_derives g u w :=
relation.refl_trans_gen.trans huv hvw

lemma CF_deri_of_deri_tran
    {u v w : list (symbol T g.nt)}
    (huv : CF_derives g u v)
    (hvw : CF_transforms g v w) :
  CF_derives g u w :=
CF_deri_of_deri_deri huv (CF_deri_of_tran hvw)

lemma CF_deri_of_tran_deri
    {u v w : list (symbol T g.nt)}
    (huv : CF_transforms g u v)
    (hvw : CF_derives g v w) :
  CF_derives g u w :=
CF_deri_of_deri_deri (CF_deri_of_tran huv) hvw

lemma CF_tran_or_id_of_deri {u w : list (symbol T g.nt)} (h : CF_derives g u w) :
  (u = w) ∨
  (∃ v : list (symbol T g.nt), (CF_transforms g u v) ∧ (CF_derives g v w)) :=
relation.refl_trans_gen.cases_head h


lemma CF_derives_with_prefix
    {oldWord newWord : list (symbol T g.nt)}
    (prefi : list (symbol T g.nt))
    (h : CF_derives g oldWord newWord) :
  CF_derives g (prefi ++ oldWord) (prefi ++ newWord) :=
begin
  induction h with a b irr hyp ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨ rule, rule_in, v, w, h_bef, h_aft ⟩,
  use rule,
  split,
  {
    exact rule_in,
  },
  use prefi ++ v,
  use w,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma CF_derives_with_postfix
    {oldWord newWord : list (symbol T g.nt)}
    (posfi : list (symbol T g.nt))
    (h : CF_derives g oldWord newWord) :
  CF_derives g (oldWord ++ posfi) (newWord ++ posfi) :=
begin
  induction h with a b irr hyp ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨ rule, rule_in, v, w, h_bef, h_aft ⟩,
  use rule,
  split,
  {
    exact rule_in,
  },
  use v,
  use w ++ posfi,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma CF_derives_with_prefix_and_postfix
    {oldWord newWord : list (symbol T g.nt)}
    (prefi posfi : list (symbol T g.nt))
    (h : CF_derives g oldWord newWord) :
  CF_derives g (prefi ++ oldWord ++ posfi) (prefi ++ newWord ++ posfi) :=
begin
  apply CF_derives_with_postfix,
  apply CF_derives_with_prefix,
  exact h,
end

end cfg_utilities


section cfg_conversion

variable {T : Type}

def csg_of_cfg (g : CF_grammar T) : CS_grammar T :=
CS_grammar.mk g.nt g.initial (list.map (λ r : g.nt × (list (symbol T g.nt)),
  csrule.mk [] r.fst [] r.snd) g.rules)

def grammar_of_cfg (g : CF_grammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map (λ r : g.nt × (list (symbol T g.nt)),
  grule.mk ([], r.fst, []) r.snd) g.rules)

lemma grammar_of_cfg_well_defined (g : CF_grammar T) :
  grammar_of_csg (csg_of_cfg g) = grammar_of_cfg g :=
begin
  unfold grammar_of_cfg,
  delta csg_of_cfg,
  delta grammar_of_csg,
  simp,
  ext1,
  simp,
  apply congr_fun,
  dsimp,
  ext1,
  cases x,
  {
    refl,
  },
  -- option.some
  apply congr_arg option.some,
  dsimp,
  rw list.append_nil,
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
      dsimp,
      rcases hyp with ⟨ r, rin, u, w, bef, aft ⟩,
      use csrule.mk [] r.fst [] r.snd,
      split,
      {
        finish,
      },
      use u,
      use w,
      split;
      dsimp;
      rw list.append_nil;
      rw list.append_nil;
      assumption,
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
      dsimp at hyp,
      rcases hyp with ⟨ r, rin, u, w, bef, aft ⟩,
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
      repeat { rw list.append_nil at * },
      split;
      dsimp;
      assumption,
    },
    exact indu (list.map symbol.terminal w),
  },
end

lemma CF_language_eq_grammar_language (g : CF_grammar T) :
  CF_language g = grammar_language (grammar_of_cfg g) :=
begin
  rw ← grammar_of_cfg_well_defined,
  rw CF_language_eq_CS_language,
  rw CS_language_eq_grammar_language,
end

theorem CF_subclass_CS (L : language T) :
  is_CF L → is_CS L :=
begin
  rintro ⟨ g, h ⟩,
  use csg_of_cfg g,
  rw ← h,
  rw CF_language_eq_CS_language,
end

end cfg_conversion
