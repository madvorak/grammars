import logic.relation
import computability.language
import list_utils


/-- Fundamental datatype; basically `τ ⊕ ν` (something like "Either tau nyy")
    where `τ` is the type of terminals and `ν` is the type of nonterminals. -/
inductive symbol (τ : Type) (ν : Type)
| terminal    : τ → symbol
| nonterminal : ν → symbol


section grammar_definitions

/-- Transformation rule for a grammar without any restrictions. -/
structure grule (τ : Type) (ν : Type) :=
(input_L : list (symbol τ ν))
(input_N : ν)
(input_R : list (symbol τ ν))
(output_string : list (symbol τ ν))

/-- Grammar (unrestricted) that generates words over the alphabet `termi` (a type of terminals). -/
structure grammar (termi : Type) :=
(nt : Type)                     -- type of nonterminals
(initial : nt)                  -- initial symbol
(rules : list (grule termi nt)) -- rewriting rules


variables {T : Type}

/-- One step of grammatical transformation. -/
def grammar_transforms (g : grammar T) (w₁ w₂ : list (symbol T g.nt)) : Prop :=
∃ r : grule T g.nt,
  r ∈ g.rules ∧
  ∃ u v : list (symbol T g.nt), and
    (w₁ = u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v)
    (w₂ = u ++ r.output_string ++ v)

/-- Any number of steps of grammatical transformation; reflexive+transitive closure of `grammar_transforms`. -/
def grammar_derives (g : grammar T) : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (grammar_transforms g)

def grammar_generates (g : grammar T) (w : list T) : Prop :=
grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

/-- Returns the set of words (lists of terminals) that can be derived from the initial nonterminal. -/
def grammar_language (g : grammar T) : language T :=
set_of (grammar_generates g)

/-- Predicate "is recursively-enumerable"; defined by an existence of a grammar for the given language. -/
def is_RE (L : language T) : Prop :=
∃ g : grammar T, grammar_language g = L

end grammar_definitions


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

lemma grammar_tran_or_id_of_deri {u w : list (symbol T g.nt)} (ass : grammar_derives g u w) :
  (u = w) ∨
  (∃ v : list (symbol T g.nt), (grammar_transforms g u v) ∧ (grammar_derives g v w)) :=
relation.refl_trans_gen.cases_head ass


lemma grammar_deri_with_prefix
    {w₁ w₂ : list (symbol T g.nt)}
    (pᵣ : list (symbol T g.nt))
    (ass : grammar_derives g w₁ w₂) :
  grammar_derives g (pᵣ ++ w₁) (pᵣ ++ w₂) :=
begin
  induction ass with x y trash hyp ih,
  {
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨r, rin, u, v, h_bef, h_aft⟩,
  use r,
  split,
  {
    exact rin,
  },
  use pᵣ ++ u,
  use v,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma grammar_deri_with_postfix
    {w₁ w₂ : list (symbol T g.nt)}
    (pₒ : list (symbol T g.nt))
    (ass : grammar_derives g w₁ w₂) :
  grammar_derives g (w₁ ++ pₒ) (w₂ ++ pₒ) :=
begin
  induction ass with x y trash hyp ih,
  {
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨r, rin, u, v, h_bef, h_aft⟩,
  use r,
  split,
  {
    exact rin,
  },
  use u,
  use v ++ pₒ,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end


def as_terminal {N : Type} : symbol T N → option T
| (symbol.terminal t)    := some t
| (symbol.nonterminal _) := none

def all_used_terminals (g : grammar T) : list T :=
list.filter_map as_terminal (list.join (list.map grule.output_string g.rules))

end grammar_utilities
