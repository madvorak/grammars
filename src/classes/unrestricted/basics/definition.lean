import logic.relation
import computability.language


/-- The type of symbols is the disjoint union of terminals and nonterminals. -/
inductive symbol (T : Type) (N : Type)
| terminal    : T → symbol
| nonterminal : N → symbol

/-- Transformation rule for a grammar without any restrictions. -/
structure grule (T : Type) (N : Type) :=
(input_L : list (symbol T N))
(input_N : N)
(input_R : list (symbol T N))
(output_string : list (symbol T N))

/-- Grammar (unrestricted) that generates words over the alphabet `T` (a type of terminals). -/
structure grammar (T : Type) :=
(nt : Type)                 -- type of nonterminals
(initial : nt)              -- initial symbol
(rules : list (grule T nt)) -- rewrite rules


variables {T : Type}

/-- One step of grammatical transformation. -/
def grammar_transforms (g : grammar T) (w₁ w₂ : list (symbol T g.nt)) : Prop :=
∃ r : grule T g.nt,
  r ∈ g.rules  ∧
  ∃ u v : list (symbol T g.nt), and
    (w₁  =  u ++  r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R  ++ v)
    (w₂  =  u ++  r.output_string  ++ v)

/-- Any number of steps of grammatical transformation; reflexive+transitive closure of `grammar_transforms`. -/
def grammar_derives (g : grammar T) : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (grammar_transforms g)

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def grammar_generates (g : grammar T) (w : list T) : Prop :=
grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

/-- The set of words that can be derived from the initial nonterminal. -/
def grammar_language (g : grammar T) : language T :=
set_of (grammar_generates g)

/-- Predicate "is recursively-enumerable"; defined by existence of a grammar for the given language. -/
def is_RE (L : language T) : Prop :=
∃ g : grammar T, grammar_language g = L
