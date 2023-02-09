import classes.unrestricted.grammar


/-- Transformation rule for a grammar in the Kuroda normal form. -/
inductive kuroda_rule (T : Type) (N : Type)
| two_two (A B C D : N)   : kuroda_rule
| one_two (A B C : N)     : kuroda_rule
| one_one (A : N) (t : T) : kuroda_rule
| one_nil (A : N)         : kuroda_rule

/-- Grammar in the Kuroda normal form that generates words
    over the alphabet `T` (a type of terminals). -/
structure kuroda_grammar (T : Type) :=
(nt : Type)
(initial : nt)
(rules : list (kuroda_rule T nt))


def grule_of_kuroda_rule {T : Type} {N : Type} : kuroda_rule T N → grule T N
| (kuroda_rule.two_two A B C D) := grule.mk [] A [symbol.nonterminal B] [symbol.nonterminal C, symbol.nonterminal D]
| (kuroda_rule.one_two A B C)   := grule.mk [] A [] [symbol.nonterminal B, symbol.nonterminal C]
| (kuroda_rule.one_one A t)     := grule.mk [] A [] [symbol.terminal t]
| (kuroda_rule.one_nil A)       := grule.mk [] A [] []

def grammar_of_kuroda_grammar {T : Type} (k : kuroda_grammar T) : grammar T :=
grammar.mk k.nt k.initial (list.map grule_of_kuroda_rule k.rules)


theorem kuroda_grammar_always_exists {T : Type} (L : language T) :
  is_RE L  →  ∃ k : kuroda_grammar T, grammar_language (grammar_of_kuroda_grammar k) = L  :=
sorry
