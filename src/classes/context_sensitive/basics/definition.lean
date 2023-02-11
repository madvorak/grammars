import classes.unrestricted.basics.definition


/-- Transformation rule for a context-sensitive grammar. -/
structure csrule (T : Type) (N : Type) :=
(context_left : list (symbol T N))
(input_nonterminal : N)
(context_right : list (symbol T N))
(output_string : list (symbol T N)) -- !! TODO require non-empty unless `S` → `[]` where `S` is on no right side !!

/-- Context-sensitive grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CS_grammar (T : Type) :=
(nt : Type)                   -- type of nonterminals
(initial : nt)                -- initial symbol
(rules : list (csrule T nt))  -- rewrite rules


variables {T : Type}

/-- One step of context-sensitive transformation. -/
def CS_transforms (g : CS_grammar T) (w₁ w₂ : list (symbol T g.nt)) : Prop :=
∃ r : csrule T g.nt, r ∈ g.rules  ∧  ∃ u v : list (symbol T g.nt), and
  (w₁ = u ++ r.context_left ++ [symbol.nonterminal r.input_nonterminal] ++ r.context_right ++ v)
  (w₂ = u ++ r.context_left ++ r.output_string ++ r.context_right ++ v)

/-- Any number of steps of context-sensitive transformation; reflexive+transitive closure of `CS_transforms`. -/
def CS_derives (g : CS_grammar T) : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CS_transforms g)

/-- Returns the set of words (lists of terminals) that can be derived from the initial nonterminal. -/
def CS_language (g : CS_grammar T) : language T :=
λ w : list T, CS_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

/-- Predicate "is context-sensitive"; defined by an existence of a context-sensitive grammar for the given language. -/
def is_CS (L : language T) : Prop :=
∃ g : CS_grammar T, CS_language g = L
