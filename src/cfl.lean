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
  (S, [a.1, S.1, c.1]),
  (S, [T.1]),
  (T, [b.1, T.1, c.1]),
  (T, []) ]

example : cfl_tranforms gramatika [b.1, S.1, b.1, a.1] [b.1, a.1, S.1, c.1, b.1, a.1] :=
begin
  unfold gramatika,
  use (S, [a.1, S.1, c.1]),
    simp,
  fconstructor,
    exact [b.1],
  fconstructor,
    exact [b.1, a.1],
  finish,
end

example : cfl_generates gramatika [a, c] :=
begin
  have step_1 : cfl_tranforms gramatika [S.1] [a.1, S.1, c.1],
  {
    unfold gramatika,
    use (S, [a.1, S.1, c.1]),
    simp,
    use [[],[]],
    finish,
  },
  have step_2 : cfl_tranforms gramatika [a.1, S.1, c.1] [a.1, T.1, c.1],
  {
    unfold gramatika,
    use (S, [T.1]),
    simp,
    use [[a.1], [c.1]],
    finish,
  },
  have step_3 : cfl_tranforms gramatika [a.1, T.1, c.1] [a.1, c.1],
  {
    unfold gramatika,
    use (T, []),
    simp,
    use [[a.1], [c.1]],
    finish,
  },
  
  have composed : cfl_derives gramatika [S.1] [a.1, c.1],
  {
    sorry,
  },
  finish,
end
