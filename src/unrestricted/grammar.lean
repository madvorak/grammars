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
