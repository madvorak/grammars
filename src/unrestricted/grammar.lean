import logic.relation
import computability.language


/-- Fundamental datatype; basically `τ ⊕ ν` (something like "Either tau nyy")
    where `τ` is the type of terminals and `ν` is the type of nonterminals. -/
inductive symbol (τ : Type) (ν : Type)
| terminal    : τ → symbol
| nonterminal : ν → symbol

structure grule (τ : Type) (ν : Type) :=
(left_side : list (symbol τ ν) × ν × list (symbol τ ν))
(right_side : list (symbol τ ν))

/-- A grammar (general) that generates words over the alphabet `termi` (a type of terminals). -/
structure grammar (termi : Type) :=
(nt : Type)                     -- type of nonterminals
(initial : nt)                  -- initial symbol
(rules : list (grule termi nt)) -- rewriting rules
