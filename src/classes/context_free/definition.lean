import classes.unrestricted.definition


/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CF_grammar (T : Type) :=
(nt : Type)                                -- type of nonterminals
(initial : nt)                             -- initial symbol
(rules : list (nt × list (symbol T nt)))   -- rewrite rules


variables {T : Type}

/-- One step of context-free transformation. -/
def CF_transforms (g : CF_grammar T) (w₁ w₂ : list (symbol T g.nt)) : Prop :=
∃ r : g.nt × list (symbol T g.nt), r ∈ g.rules ∧ ∃ u v : list (symbol T g.nt), and
  (w₁ = u ++ [symbol.nonterminal r.fst] ++ v)
  (w₂ = u ++ r.snd ++ v)

/-- Any number of steps of context-free transformation; reflexive+transitive closure of `CF_transforms`. -/
def CF_derives (g : CF_grammar T) : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CF_transforms g)

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def CF_generates (g : CF_grammar T) (w : list T) : Prop :=
CF_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

/-- Context-free language; just a wrapper around `CF_generates`. -/
def CF_language (g : CF_grammar T) : language T :=
set_of (CF_generates g)

/-- Predicate "is context-free"; defined by an existence of a context-free grammar for the given language. -/
def is_CF (L : language T) : Prop :=
∃ g : CF_grammar T, CF_language g = L
