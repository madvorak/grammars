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

/-- Accepts a string (a list of symbols) iff it can be derived from the initial nonterminal. -/
def CS_generates_str (str : list (symbol T g.nt)) : Prop :=
CS_derives g [symbol.nonterminal g.initial] str

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def CS_generates (word : list T) : Prop :=
CS_generates_str g (list.map symbol.terminal word)

def CS_language : language T :=
CS_generates g

end csg_definitions


section csg_to_grammar

def grammar_of_csg {T : Type} (g : CS_grammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map 
  (λ r : csrule T g.nt, grule.mk
    (r.context_left, r.input_nonterminal, r.context_right)
    (r.context_left ++ r.output_string ++ r.context_right)
  ) g.rules)

end csg_to_grammar
