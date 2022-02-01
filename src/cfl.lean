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

def cfl_tranforms (gr : CFgrammar) (oldWord newWord : list symbol) : Prop :=
∃ r ∈ gr.rules, ∃ v w : list symbol, oldWord = v ++ [prod.fst r] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def cfl_derives (gr : CFgrammar) := relation.refl_trans_gen (cfl_tranforms gr)

def cfl_generates (gr : CFgrammar) (word : list symbol) : Prop :=
cfl_derives gr [gr.initial] word


-- Demonstrations

def gramatika := CFgrammar.mk symbol.S [
  (symbol.S, [symbol.a, symbol.S, symbol.c]),
  (symbol.S, [symbol.T]),
  (symbol.T, [symbol.b, symbol.T, symbol.c]),
  (symbol.T, []) ]

example : cfl_tranforms gramatika [symbol.b, symbol.S, symbol.b, symbol.a]
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

example : cfl_generates gramatika [symbol.a, symbol.c] :=
begin
  have step_1 : cfl_tranforms gramatika [symbol.S] [symbol.a, symbol.S, symbol.c],
  {
    unfold gramatika,
    use (symbol.S, [symbol.a, symbol.S, symbol.c]),
    simp,
    use [[],[]],
    finish,
  },
  have step_2 : cfl_tranforms gramatika [symbol.a, symbol.S, symbol.c] [symbol.a, symbol.T, symbol.c],
  {
    unfold gramatika,
    use (symbol.S, [symbol.T]),
    simp,
    use [[symbol.a], [symbol.c]],
    finish,
  },
  have step_3 : cfl_tranforms gramatika [symbol.a, symbol.T, symbol.c] [symbol.a, symbol.c],
  {
    unfold gramatika,
    use (symbol.T, []),
    simp,
    use [[symbol.a], [symbol.c]],
    finish,
  },
  
  have composed : cfl_derives gramatika [symbol.S] [symbol.a, symbol.c],
  {
    --simp [step_1, step_2, step_3],
    fconstructor,
      exact [symbol.a, symbol.S, symbol.c],
    --simp [step_1],
    sorry,
    sorry,
  },
  finish,
end
