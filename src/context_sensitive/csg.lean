import unrestricted.grammar


section csg_definitions

/-- Transformation rule for a context-sensitive grammar. -/
structure csrule (τ : Type) (ν : Type) :=
(context_left : list (symbol τ ν))
(input_nonterminal : ν)
(context_right : list (symbol τ ν))
(output_string : list (symbol τ ν))

/-- Context-sensitive grammar that generates words over the alphabet `termi` (a type of terminals). -/
structure CS_grammar (termi : Type) :=
(nt : Type)                                  -- type of nonterminals
(initial : nt)                               -- initial symbol
(rules : list (csrule termi nt))             -- rewriting rules


variables {T : Type} (g : CS_grammar T)

/-- One step of context-sensitive transformation. -/
def CS_transforms (oldWord newWord : list (symbol T g.nt)) : Prop :=
∃ r : csrule T g.nt, r ∈ g.rules  ∧  ∃ v w : list (symbol T g.nt), and
    (oldWord = v ++ r.context_left ++ [symbol.nonterminal r.input_nonterminal] ++ r.context_right ++ w)
    (newWord = v ++ r.context_left ++                     r.output_string      ++ r.context_right ++ w)

/-- Any number of steps of context-sensitive transformation; reflexive+transitive closure of `CS_transforms`. -/
def CS_derives : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CS_transforms g)

/-- Returns the set of words (lists of terminals) that can be derived from the initial nonterminal. -/
def CS_language : language T :=
λ w : list T, CS_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

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
  (h : CS_derives g u w) :  or  (u = w)
    (∃ v : list (symbol T g.nt), (CS_transforms g u v) ∧ (CS_derives g v w)) :=
relation.refl_trans_gen.cases_head h

end csg_utilities


section csg_conversion

def grammar_of_csg {T : Type} (g : CS_grammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map 
  (λ r : csrule T g.nt, grule.mk
    (r.context_left, r.input_nonterminal, r.context_right)
    (r.context_left ++ r.output_string ++ r.context_right)
  ) g.rules)

lemma CS_language_eq_grammar_language {T : Type} (g : CS_grammar T) :
  CS_language g = grammar_language (grammar_of_csg g) :=
sorry

end csg_conversion
