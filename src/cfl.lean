import tactic
import logic.relation


-- Definitions

inductive symbol --: Type
| a --: symbol
| b --: symbol
| c --: symbol
| S --: symbol
| T --: symbol

def nonterminal := subtype (λ x : symbol, x = symbol.S ∨ x = symbol.T)

--def nonter := {x : symbol // x = symbol.S ∨ x = symbol.T}
--def n₁ : nonterminal := nonterminal.mk.S
--#print nonterminal
--#print nonter
--#eval nonter = nonterminal

structure CFgrammar :=
(initial : symbol)
(rules : list (symbol × list symbol))

#print CFgrammar

def tranforms (gr : CFgrammar) (oldWord newWord : list symbol) : Prop :=
∃ r ∈ gr.rules, ∃ v w : list symbol, oldWord = v ++ [prod.fst r] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

--def derives (gr : CFgrammar) := relation.refl_trans_gen (λ x : list symbol, λ y : list symbol, transforms gr x y)



-- Demonstrations

def gramatika := CFgrammar.mk symbol.S [
  (symbol.S, [symbol.a, symbol.S, symbol.c]),
  (symbol.S, [symbol.T]),
  (symbol.T, [symbol.b, symbol.T, symbol.c]),
  (symbol.T, []) ]

example : tranforms gramatika [symbol.b, symbol.S, symbol.b, symbol.a]
                    [symbol.b, symbol.a, symbol.S, symbol.c, symbol.b, symbol.a] :=
begin
  unfold gramatika,
  use (symbol.S, [symbol.a, symbol.S, symbol.c]),
    simp,
  fconstructor,
    exact [symbol.b],
  fconstructor,
    exact [symbol.b, symbol.a],
  finish,
end
