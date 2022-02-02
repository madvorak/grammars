import tactic
import logic.relation


-- Definitions

inductive symbol
| a
| b
| c
| S
| T

def is_nonterminal (x : symbol) : Prop := x = symbol.S ∨ x = symbol.T

def nonterminal := {x : symbol // is_nonterminal x}

def terminal := {x : symbol // ¬ is_nonterminal x}

def nS : nonterminal := subtype.mk symbol.S
begin
  left,
  refl,
end

def nT : nonterminal := subtype.mk symbol.T
begin
  right,
  refl,
end

structure CFgrammar :=
(initial : nonterminal)
(rules : list (nonterminal × list symbol))

def cfl_tranforms (gr : CFgrammar) (oldWord newWord : list symbol) : Prop :=
∃ r ∈ gr.rules, ∃ v w : list symbol, oldWord = v ++ [subtype.val (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def cfl_derives (gr : CFgrammar) := relation.refl_trans_gen (cfl_tranforms gr)

def cfl_generates (gr : CFgrammar) (word : list terminal) : Prop :=
cfl_derives gr [subtype.val gr.initial] (list.map subtype.val word)


-- Demonstrations

def gramatika := CFgrammar.mk nS [
  (nS, [symbol.a, symbol.S, symbol.c]),
  (nS, [symbol.T]),
  (nT, [symbol.b, symbol.T, symbol.c]),
  (nT, []) ]

example : cfl_tranforms gramatika [symbol.b, symbol.S, symbol.b, symbol.a]
                        [symbol.b, symbol.a, symbol.S, symbol.c, symbol.b, symbol.a] :=
begin
  unfold gramatika,
  use (nS, [symbol.a, symbol.S, symbol.c]),
    simp,
  fconstructor,
    exact [symbol.b],
  fconstructor,
    exact [symbol.b, symbol.a],
  finish,
end

example : cfl_generates gramatika [subtype.mk symbol.a sorry, subtype.mk symbol.c sorry] :=
begin
  have step_1 : cfl_tranforms gramatika [symbol.S] [symbol.a, symbol.S, symbol.c],
  {
    unfold gramatika,
    use (nS, [symbol.a, symbol.S, symbol.c]),
    simp,
    use [[],[]],
    finish,
  },
  have step_2 : cfl_tranforms gramatika [symbol.a, symbol.S, symbol.c] [symbol.a, symbol.T, symbol.c],
  {
    unfold gramatika,
    use (nS, [symbol.T]),
    simp,
    use [[symbol.a], [symbol.c]],
    finish,
  },
  have step_3 : cfl_tranforms gramatika [symbol.a, symbol.T, symbol.c] [symbol.a, symbol.c],
  {
    unfold gramatika,
    use (nT, []),
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
