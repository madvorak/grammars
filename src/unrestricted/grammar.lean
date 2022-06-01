import logic.relation
import computability.language
import triplets_utilities


/-- Fundamental datatype; basically `τ ⊕ ν` (something like "Either tau nyy")
    where `τ` is the type of terminals and `ν` is the type of nonterminals. -/
inductive symbol (τ : Type) (ν : Type)
| terminal    : τ → symbol
| nonterminal : ν → symbol


section grammar_definitions

/-- Transformation rule for a grammar without any restrictions. -/
structure grule (τ : Type) (ν : Type) :=
(input_string : list (symbol τ ν) × ν × list (symbol τ ν))
(output_string : list (symbol τ ν))

/-- Grammar (general) that generates words over the alphabet `termi` (a type of terminals). -/
structure grammar (termi : Type) :=
(nt : Type)                     -- type of nonterminals
(initial : nt)                  -- initial symbol
(rules : list (grule termi nt)) -- rewriting rules


variables {T : Type} (g : grammar T)

/-- One step of grammatical transformation. -/
def grammar_transforms (oldWord newWord : list (symbol T g.nt)) : Prop :=
∃ r : grule T g.nt,
  r ∈ g.rules ∧
  ∃ v w : list (symbol T g.nt), and
    (oldWord = v ++ r.input_string.first ++ [symbol.nonterminal r.input_string.secon] ++ r.input_string.third ++ w)
    (newWord = v ++ r.output_string ++ w)

/-- Any number of steps of grammatical transformation; reflexive+transitive closure of `grammar_transforms`. -/
def grammar_derives : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (grammar_transforms g)

/-- Returns the set of words (lists of terminals) that can be derived from the initial nonterminal. -/
def grammar_language : language T :=
λ w : list T, grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

end grammar_definitions

/-- Predicate "is recursively-enumerable"; defined by an existence of a grammar for the given language. -/
def is_RE {T : Type} (L : language T) : Prop :=
∃ g : grammar T, grammar_language g = L


section grammar_utilities
variables {T : Type} {g : grammar T}

/-- The relation `grammar_derives` is reflexive. -/
lemma grammar_deri_self {w : list (symbol T g.nt)} :
  grammar_derives g w w :=
relation.refl_trans_gen.refl

lemma grammar_deri_of_tran {v w : list (symbol T g.nt)} :
  grammar_transforms g v w → grammar_derives g v w :=
relation.refl_trans_gen.single

/-- The relation `grammar_derives` is transitive. -/
lemma grammar_deri_of_deri_deri {u v w : list (symbol T g.nt)}
  (huv : grammar_derives g u v) (hvw : grammar_derives g v w) :
    grammar_derives g u w :=
relation.refl_trans_gen.trans huv hvw

lemma grammar_deri_of_deri_tran {u v w : list (symbol T g.nt)}
  (huv : grammar_derives g u v) (hvw : grammar_transforms g v w) :
    grammar_derives g u w :=
grammar_deri_of_deri_deri huv (grammar_deri_of_tran hvw)

lemma grammar_deri_of_tran_deri {u v w : list (symbol T g.nt)}
  (huv : grammar_transforms g u v) (hvw : grammar_derives g v w) :
    grammar_derives g u w :=
grammar_deri_of_deri_deri (grammar_deri_of_tran huv) hvw

lemma grammar_tran_or_id_of_deri {u w : list (symbol T g.nt)}
  (h : grammar_derives g u w) :  or  (u = w)
    (∃ v : list (symbol T g.nt), (grammar_transforms g u v) ∧ (grammar_derives g v w)) :=
relation.refl_trans_gen.cases_head h

end grammar_utilities
