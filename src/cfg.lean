import data.fintype.basic
import logic.relation
import computability.language


section cfg_def

inductive symbol (τ : Type) (ν : Type)
| terminal    : τ → symbol
| nonterminal : ν → symbol

structure CF_grammar (termi : Type) :=
(nt : Type)
(initial : nt)
(rules : list (nt × (list (symbol termi nt))))

end cfg_def


section cfg_derivations
variables {T : Type} (g : CF_grammar T)

def CF_transforms (oldWord newWord : list (symbol T g.nt)) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbol T g.nt), 
  oldWord = v ++ [symbol.nonterminal (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def CF_derives : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CF_transforms g)

def CF_generates_str (str : list (symbol T g.nt)) : Prop :=
CF_derives g [symbol.nonterminal g.initial] str

def CF_generates (word : list T) : Prop :=
CF_generates_str g (list.map symbol.terminal word)

def CF_language : language T :=
CF_generates g

end cfg_derivations


section cfg_cfl

def is_CF {T : Type} (L : language T) :=
∃ g : CF_grammar T, CF_language g = L

end cfg_cfl


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

def gramatika : CF_grammar (fin 3) := CF_grammar.mk (fin 2) S_ [
  (S_, [a, S, c]),
  (S_, [R]),
  (R_, [b, R, c]),
  (R_, [])
]

example : CF_generates gramatika [a_, a_, b_, c_, c_, c_] :=
begin
  unfold gramatika,

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
      finish,
    },
    use [[a, a, b], [c, c, c]],
    simp,
    repeat { try {split}, try {refl} },
  },
end

end cfg_demonstrations
