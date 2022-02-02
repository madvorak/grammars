import tactic
import logic.relation


-- Definitions (important)

inductive symbol
| _a
| _b
| _c
| _S
| _T


def is_terminal (x : symbol) : Prop := x ∈ [symbol._a, symbol._b, symbol._c]

@[reducible] def terminal := {x : symbol // is_terminal x}

@[reducible] def nonterminal := {x : symbol // ¬ is_terminal x}


structure CF_grammar :=
(initial : nonterminal)
(rules : list (nonterminal × list symbol))

def CF_tranforms (gr : CF_grammar) (oldWord newWord : list symbol) : Prop :=
∃ r ∈ gr.rules, ∃ v w : list symbol, 
  oldWord = v ++ [subtype.val (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def CF_derives (gr : CF_grammar) := relation.refl_trans_gen (CF_tranforms gr)

def CF_generates (gr : CF_grammar) (word : list terminal) : Prop :=
CF_derives gr [subtype.val gr.initial] (list.map subtype.val word)


-- Definitions (supplementary)

meta def trivi_terminal : tactic unit :=
`[ unfold is_terminal, finish ]

def a : terminal := subtype.mk symbol._a (by trivi_terminal)

def b : terminal := subtype.mk symbol._b (by trivi_terminal)

def c : terminal := subtype.mk symbol._c (by trivi_terminal)


meta def trivi_nonterminal : tactic unit :=
`[ intro h, unfold is_terminal at h, finish ]

def S : nonterminal := subtype.mk symbol._S (by trivi_nonterminal)

def T : nonterminal := subtype.mk symbol._T (by trivi_nonterminal)



-- Demonstrations

def gramatika := CF_grammar.mk S [
  (S, [a, S, c]),
  (S, [T]),
  (T, [b, T, c]),
  (T, []) ]

example : CF_tranforms gramatika [b, S, b, a] [b, a, S, c, b, a] :=
begin
  unfold gramatika,
  use (S, [a, S, c]),
    simp,
  fconstructor,
    exact [b],
  fconstructor,
    exact [b, a],
  finish,
end

example : CF_derives gramatika [a, T] [a, b, c] :=
begin
  fconstructor,
    exact [a, b, T, c],
  fconstructor,
    exact [a, T],
  refl,
  {
    use (T, [b, T, c]),
    split,
      unfold gramatika,
      simp,
    use [[a], []],
    finish,
  },
  {
    use (T, []),
    split,
      unfold gramatika,
      simp,
    use [[a, b], [c]],
    finish,
  }
end

example : CF_generates gramatika [a, c] :=
begin
  have step_1 : CF_tranforms gramatika [S] [a, S, c],
  {
    unfold gramatika,
    use (S, [a, S, c]),
    simp,
    use [[],[]],
    finish,
  },
  have step_2 : CF_tranforms gramatika [a, S, c] [a, T, c],
  {
    unfold gramatika,
    use (S, [T]),
    simp,
    use [[a], [c]],
    finish,
  },
  have step_3 : CF_tranforms gramatika [a, T, c] [a, c],
  {
    unfold gramatika,
    use (T, []),
    simp,
    use [[a], [c]],
    finish,
  },
  
  have composed : CF_derives gramatika [S] [a, c],
  {
    fconstructor,
      exact [a, T, c],
    fconstructor,
      exact [a, S, c],
    fconstructor,
      exact [S],
    refl,
    exact step_1,
    exact step_2,
    exact step_3,
  },
  finish,
end
