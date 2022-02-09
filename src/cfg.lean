import data.fintype.basic
import logic.relation
import computability.language


section cfg_grammars

inductive symbol (τ : Type) (ν : Type) [fintype τ] [fintype ν]
| terminal    : τ → symbol
| nonterminal : ν → symbol

structure CF_grammar (termin : Type) (nontermin : Type)
  [fintype termin] [fintype nontermin] :=
(initial : nontermin)
(rules : list (nontermin × (list (symbol termin nontermin))))

end cfg_grammars


section cfg_derivations
variables {T N : Type} [fintype T] [fintype N] (g : CF_grammar T N)

def CF_transforms (oldWord newWord : list (symbol T N)) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbol T N), 
  oldWord = v ++ [symbol.nonterminal (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def CF_derives : list (symbol T N) → list (symbol T N) → Prop :=
relation.refl_trans_gen (CF_transforms g)

def CF_generates_str (str : list (symbol T N)) : Prop :=
CF_derives g [symbol.nonterminal g.initial] str

def CF_generates (word : list T) : Prop :=
CF_generates_str g (list.map symbol.terminal word)

def CF_language : language T :=
CF_generates g

end cfg_derivations



section cfg_demonstrations

def a_ : fin 3 := 0
def a : symbol (fin 3) (fin 2) := symbol.terminal a_

def b_ : fin 3 := 1
def b : symbol (fin 3) (fin 2) := symbol.terminal b_

def c_ : fin 3 := 2
def c : symbol (fin 3) (fin 2) := symbol.terminal c_

def S_ : fin 2 := 0
def S : symbol (fin 3) (fin 2) := symbol.nonterminal S_

def R_ : fin 2 := 1
def R : symbol (fin 3) (fin 2) := symbol.nonterminal R_

def gramatika : CF_grammar (fin 3) (fin 2) := CF_grammar.mk S_ [
  (S_, [a, S, c]),
  (S_, [R]),
  (R_, [b, R, c]),
  (R_, [])
]

example : CF_generates gramatika [a_, a_, b_, c_, c_, c_] :=
begin
  fconstructor,
    exact [a, a, b, R, c, c, c],
  fconstructor,
    exact [a, a, R, c, c],
  fconstructor,
    exact [a, a, S, c, c],
  fconstructor,
    exact [a, S, c],
  fconstructor,
    exact [S],
  refl,
  {
    use (S_, [a, S, c]),
    split,
    {
      unfold gramatika,
      finish,
    },
    use [[], []],
    simp,
    refl,
  },
  {
    use (S_, [a, S, c]),
    split,
    {
      unfold gramatika,
      finish,
    },
    use [[a], [c]],
    simp,
    refl,
  },
  {
    use (S_, [R]),
    split,
    {
      unfold gramatika,
      finish,
    },
    use [[a, a], [c, c]],
    simp,
    refl,
  },
  {
    use (R_, [b, R, c]),
    split,
    {
      unfold gramatika,
      finish,
    },
    use [[a, a], [c, c]],
    simp,
    refl,
  },
  {
    simp,
    use (R_, []),
    split,
    {
      unfold gramatika,
      finish,
    },
    use [[a, a, b], [c, c, c]],
    simp,
    repeat { try {split}, try {refl} },
  },
end

end cfg_demonstrations