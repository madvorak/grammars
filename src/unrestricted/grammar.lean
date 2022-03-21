import logic.relation
import computability.language


/-- Fundamental datatype; basically `τ ⊕ ν` (something like "Either tau nyy")
    where `τ` is the type of terminals and `ν` is the type of nonterminals. -/
inductive symbol (τ : Type) (ν : Type)
| terminal    : τ → symbol
| nonterminal : ν → symbol

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
∃ r : grule T g.nt, r ∈ g.rules  ∧  ∃ v w : list (symbol T g.nt),
  oldWord = v ++ r.input_string.fst ++ [symbol.nonterminal r.input_string.snd.fst] ++ r.input_string.snd.snd ++ w
  ∧  newWord = v ++ r.output_string ++ w

/-- Any number of steps of grammatical transformation; reflexive+transitive closure of `grammar_transforms`. -/
def grammar_derives : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (grammar_transforms g)

/-- Accepts a string (a list of symbols) iff it can be derived from the initial nonterminal. -/
def grammar_generates_str (str : list (symbol T g.nt)) : Prop :=
grammar_derives g [symbol.nonterminal g.initial] str

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def grammar_generates (word : list T) : Prop :=
grammar_generates_str g (list.map symbol.terminal word)

def grammar_language : language T :=
grammar_generates g
