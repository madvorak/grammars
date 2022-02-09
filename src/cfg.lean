import logic.relation
import data.fintype.basic
import computability.language


inductive symbol (τ : Type) (μ : Type) [fintype τ] [fintype μ]
| terminal : τ → symbol
| nonterminal : μ →  symbol

structure CF_grammar (terminal : Type) (nonterminal : Type)
  [fintype terminal] [fintype nonterminal] :=
(initial : nonterminal)
(rules : list (nonterminal × (list (symbol terminal nonterminal))))


variables {T N : Type} [fintype T] [fintype N] (g : CF_grammar T N)

def CF_transforms (oldWord newWord : list (symbol T N)) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbol T N), 
  oldWord = v ++ [symbol.nonterminal (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def CF_derives : list (symbol T N) → list (symbol T N) → Prop :=
relation.refl_trans_gen (CF_transforms g)

def CF_generates (word : list (symbol T N)) : Prop :=
CF_derives g [symbol.nonterminal g.initial] word

def CF_language : language (symbol T N) :=
CF_generates g
