import logic.relation
import tactic
import computability.language


inductive symbol (τ : Type) (μ : Type) [fintype τ] [fintype μ]
| terminal : τ → symbol
| nonterminal : μ →  symbol

#check symbol

#check list (ℕ × (list char))

def aa : (fin 5) := 2
def bb : (fin 7) := 6

#check symbol (fin 5) (fin 7)

def tt := symbol (fin 5) (fin 7)

def tta : tt := symbol.terminal aa
def ttb : tt := symbol.nonterminal bb

#check tta
#check ttb

def parek : ((fin 5) × (list tt)) := (aa, [tta, ttb])

#check parek
#print parek

structure CF_grammar (terminal : Type) (nonterminal : Type)
  [fintype terminal] [fintype nonterminal] :=
(initial : nonterminal)
(rules : list (nonterminal × (list (symbol terminal nonterminal))))


def CF_transforms {T N : Type} [fintype T] [fintype N] 
  (gr : CF_grammar T N) (oldWord newWord : list (symbol T N)) : Prop :=
∃ r ∈ gr.rules, ∃ v w : list (symbol T N), 
  oldWord = v ++ [symbol.nonterminal (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def CF_derives {T N : Type} [fintype T] [fintype N] 
  (gr : CF_grammar T N) : list (symbol T N) → list (symbol T N) → Prop :=
relation.refl_trans_gen (CF_transforms gr)

def CF_generates {T N : Type} [fintype T] [fintype N]
  (gr : CF_grammar T N) (word : list (symbol T N)) : Prop :=
CF_derives gr [symbol.nonterminal gr.initial] word

def CF_language {T N : Type} [fintype T] [fintype N]
  (gr : CF_grammar T N) : language (symbol T N) :=
CF_generates gr
