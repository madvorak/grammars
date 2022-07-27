import unrestricted.grammar


section csg_definitions

/-- Transformation rule for a context-sensitive grammar. -/
structure csrule (τ : Type) (ν : Type) :=
(context_left : list (symbol τ ν))
(input_nonterminal : ν)
(context_right : list (symbol τ ν))
(output_string : list (symbol τ ν)) -- !! TODO require non-empty unless `S` → `[]` where `S` is on no right side !!

/-- Context-sensitive grammar that generates words over the alphabet `termi` (a type of terminals). -/
structure CS_grammar (termi : Type) :=
(nt : Type)                                  -- type of nonterminals
(initial : nt)                               -- initial symbol
(rules : list (csrule termi nt))             -- rewriting rules


variables {T : Type}

/-- One step of context-sensitive transformation. -/
def CS_transforms (g : CS_grammar T) (w₁ w₂ : list (symbol T g.nt)) : Prop :=
∃ r : csrule T g.nt, r ∈ g.rules  ∧  ∃ u v : list (symbol T g.nt), and
  (w₁ = u ++ r.context_left ++ [symbol.nonterminal r.input_nonterminal] ++ r.context_right ++ v)
  (w₂ = u ++ r.context_left ++                     r.output_string      ++ r.context_right ++ v)

/-- Any number of steps of context-sensitive transformation; reflexive+transitive closure of `CS_transforms`. -/
def CS_derives (g : CS_grammar T) : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CS_transforms g)

/-- Returns the set of words (lists of terminals) that can be derived from the initial nonterminal. -/
def CS_language (g : CS_grammar T) : language T :=
λ w : list T, CS_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

/-- Predicate "is context-sensitive"; defined by an existence of a context-sensitive grammar for the given language. -/
def is_CS (L : language T) : Prop :=
∃ g : CS_grammar T, CS_language g = L

end csg_definitions


section csg_utilities
variables {T : Type} {g : CS_grammar T}

/-- The relation `CS_derives` is reflexive. -/
lemma CS_deri_self {w : list (symbol T g.nt)} :
  CS_derives g w w :=
relation.refl_trans_gen.refl

lemma CS_deri_of_tran {v w : list (symbol T g.nt)} :
  CS_transforms g v w → CS_derives g v w :=
relation.refl_trans_gen.single

/-- The relation `CS_derives` is transitive. -/
lemma CS_deri_of_deri_deri {u v w : list (symbol T g.nt)}
  (huv : CS_derives g u v) (hvw : CS_derives g v w) :
    CS_derives g u w :=
relation.refl_trans_gen.trans huv hvw

lemma CS_deri_of_deri_tran {u v w : list (symbol T g.nt)}
  (huv : CS_derives g u v) (hvw : CS_transforms g v w) :
    CS_derives g u w :=
CS_deri_of_deri_deri huv (CS_deri_of_tran hvw)

lemma CS_deri_of_tran_deri {u v w : list (symbol T g.nt)}
  (huv : CS_transforms g u v) (hvw : CS_derives g v w) :
    CS_derives g u w :=
CS_deri_of_deri_deri (CS_deri_of_tran huv) hvw

lemma CS_tran_or_id_of_deri {u w : list (symbol T g.nt)}
  (ass : CS_derives g u w) :  or  (u = w)
    (∃ v : list (symbol T g.nt), (CS_transforms g u v) ∧ (CS_derives g v w)) :=
relation.refl_trans_gen.cases_head ass

end csg_utilities


section csg_conversion

variables {T : Type}

def grammar_of_csg (g : CS_grammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map 
  (λ r : csrule T g.nt, grule.mk
    (r.context_left, r.input_nonterminal, r.context_right)
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
      intros v h,
      induction h with x y trash hyp ih,
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
      dsimp,
      rcases hyp with ⟨ r, rin, u, w, bef, aft ⟩,
      use grule.mk
        (r.context_left, r.input_nonterminal, r.context_right)
        (r.context_left ++ r.output_string ++ r.context_right),
      split,
      {
        finish,
      },
      use u,
      use w,
      repeat { rw list.append_nil at * },
      split,
      {
        exact bef,
      },
      dsimp,
      rw ← list.append_assoc,
      rw ← list.append_assoc,
      exact aft,
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
      intros v h,
      induction h with x y trash hyp ih,
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
      dsimp at hyp,
      rcases hyp with ⟨ r, rin, u, w, bef, aft ⟩,
      simp at rin,
      rcases rin with ⟨ new_rule, new_rule_in, new_rule_def ⟩,
      use new_rule,
      split,
      {
        exact new_rule_in,
      },
      use u,
      use w,
      split,
      {
        rw ← new_rule_def at bef,
        exact bef,
      },
      {
        rw ← new_rule_def at aft,
        dsimp at aft,
        rw ← list.append_assoc at aft,
        rw ← list.append_assoc at aft,
        exact aft,
      },
    },
    exact indu (list.map symbol.terminal w),
  },
end

theorem CS_subclass_Enumerable (L : language T) :
  is_CS L → is_RE L :=
begin
  rintro ⟨ g, h ⟩,
  use grammar_of_csg g,
  rw ← h,
  rw CS_language_eq_grammar_language,
end

end csg_conversion
