import tactic
import logic.relation

-- Definitions

inductive symbol
| _a
| _b
| _c
| _S
| _T

def is_terminal (x : symbol) : Prop := x ∈ [symbol._a, symbol._b, symbol._c]

def terminal := {x : symbol // is_terminal x}

def nonterminal := {x : symbol // ¬ is_terminal x}

def a : terminal := subtype.mk symbol._a
begin
  unfold is_terminal,
  finish,
end

def b : terminal := subtype.mk symbol._b
begin
  unfold is_terminal,
  finish,
end

def c : terminal := subtype.mk symbol._c
begin
  unfold is_terminal,
  finish,
end

def S : nonterminal := subtype.mk symbol._S
begin
  intro h,
  unfold is_terminal at h,
  finish,
end

def T : nonterminal := subtype.mk symbol._T
begin
  intro h,
  unfold is_terminal at h,
  finish,
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

def gramatika := CFgrammar.mk S [
  (S, [symbol._a, symbol._S, symbol._c]),
  (S, [symbol._T]),
  (T, [symbol._b, symbol._T, symbol._c]),
  (T, []) ]

example : cfl_tranforms gramatika [symbol._b, symbol._S, symbol._b, symbol._a]
                       [symbol._b, symbol._a, symbol._S, symbol._c, symbol._b, symbol._a] :=
begin
  unfold gramatika,
  use (S, [symbol._a, symbol._S, symbol._c]),
    simp,
  fconstructor,
    exact [symbol._b],
  fconstructor,
    exact [symbol._b, symbol._a],
  finish,
end

example : cfl_generates gramatika [a, c] :=
begin
  have step_1 : cfl_tranforms gramatika [symbol._S] [symbol._a, symbol._S, symbol._c],
  {
    unfold gramatika,
    use (S, [symbol._a, symbol._S, symbol._c]),
    simp,
    use [[],[]],
    finish,
  },
  have step_2 : cfl_tranforms gramatika [symbol._a, symbol._S, symbol._c] [symbol._a, symbol._T, symbol._c],
  {
    unfold gramatika,
    use (S, [symbol._T]),
    simp,
    use [[symbol._a], [symbol._c]],
    finish,
  },
  have step_3 : cfl_tranforms gramatika [symbol._a, symbol._T, symbol._c] [symbol._a, symbol._c],
  {
    unfold gramatika,
    use (T, []),
    simp,
    use [[symbol._a], [symbol._c]],
    finish,
  },
  
  have composed : cfl_derives gramatika [symbol._S] [symbol._a, symbol._c],
  {
    --simp [step_1, step_2, step_3],
    fconstructor,
      exact [symbol._a, symbol._S, symbol._c],
    --simp [step_1],
    sorry,
    sorry,
  },
  finish,
end
