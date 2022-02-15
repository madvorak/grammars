import data.fintype.basic
import logic.relation
import computability.language


inductive symbol (τ : Type) (ν : Type) [fintype τ] [fintype ν]
| terminal    : τ → symbol
| nonterminal : ν → symbol


section def_grammars
variables (T : Type) (N : Type) [fintype T] [fintype N]

structure grammar :=
(initial : N)
(rules : list (prod
  {str : list (symbol T N) // ∃ n : N, (symbol.nonterminal n) ∈ str}
  (list (symbol T N))
))

structure noncontracting extends grammar T N :=
(len_non_decr : 
  ∀ r : (prod
    {str : list (symbol T N) // ∃ n : N, (symbol.nonterminal n) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → 
    (r.fst.val.length ≤ r.snd.length)
)

structure noncontracting_with_empty_word extends grammar T N :=
(len_non_decr_or_snd_empty : 
  ∀ r : (prod
    {str : list (symbol T N) // ∃ n : N, (symbol.nonterminal n) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → or
    ((r.fst.val.length ≤ r.snd.length) ∧ (symbol.nonterminal initial ∉ r.snd))
    ((r.fst.val = [symbol.nonterminal initial]) ∧ (r.snd = []))
)

structure kuroda_normal_form extends noncontracting_with_empty_word T N :=
(kuroda_condition :
  ∀ r : (prod
    {str : list (symbol T N) // ∃ n : N, (symbol.nonterminal n) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → (
    ∃ A B C D : N, and
      (r.fst.val = [symbol.nonterminal A, symbol.nonterminal B])
      (r.snd     = [symbol.nonterminal C, symbol.nonterminal D])
  ) ∨ (
    ∃ X Y Z : N, and
      (r.fst.val = [symbol.nonterminal X])
      (r.snd     = [symbol.nonterminal Y, symbol.nonterminal Z])
  ) ∨ (
    ∃ R : N, ∃ a : T, and
      (r.fst.val = [symbol.nonterminal R])
      (r.snd     = [symbol.terminal a])  
  ) ∨ (  
      (r.fst.val = [symbol.nonterminal initial]) ∧ (r.snd = [])
  )
)

structure context_free extends grammar T N :=
(fst_singleton_nonterminal :
  ∀ r : (prod
    {str : list (symbol T N) // ∃ n : N, (symbol.nonterminal n) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → 
    (∃ n : N, r.fst.val = [symbol.nonterminal n])
)

structure left_linear extends context_free T N :=
(snd_max_one_nonterminal :
  ∀ r : (prod
    {str : list (symbol T N) // ∃ n : N, (symbol.nonterminal n) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → 
    (∃ n : N, ∃ ts : list T, or
      (r.snd = list.map symbol.terminal ts)
      (r.snd = symbol.nonterminal n :: (list.map symbol.terminal ts))
    )
)

structure right_linear extends context_free T N :=
(snd_max_one_nonterminal :
  ∀ r : (prod
    {str : list (symbol T N) // ∃ n : N, (symbol.nonterminal n) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → 
    (∃ ts : list T, ∃ n : N, or
      (r.snd = list.map symbol.terminal ts)
      (r.snd = (list.map symbol.terminal ts) ++ [symbol.nonterminal n])
    )
)

end def_grammars


section def_derivations
variables {T N : Type} [fintype T] [fintype N] (g : grammar T N)

def letter := symbol T N

def grammar_transforms (oldWord newWord : list letter) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbol T N), 
  oldWord = (v ++ subtype.val (prod.fst r) ++ w) ∧ (newWord = v ++ (prod.snd r) ++ w)

def grammar_derives : list letter → list letter → Prop := 
relation.refl_trans_gen (grammar_transforms g)

def grammar_generates_str (str : list letter) : Prop :=
grammar_derives g [symbol.nonterminal g.initial] str

def grammar_generates (word : list T) : Prop :=
grammar_generates_str g (list.map symbol.terminal word)

def grammar_language : language T :=
grammar_generates g

end def_derivations



section demo

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

def gramatika : grammar (fin 3) (fin 2) := grammar.mk S_ [
  ((subtype.mk [S] (by { use S_, finish })), [a, S, c]),
  ((subtype.mk [S] (by { use S_, finish })), [R]),
  ((subtype.mk [R] (by { use R_, finish })), [b, R, c]),
  ((subtype.mk [R] (by { use R_, finish })), [])
]

def bezkontextova : context_free (fin 3) (fin 2) := context_free.mk gramatika
begin
  intro r,
  intro rr,
  unfold gramatika at rr,
  simp at rr,
  cases rr with r1 foo,
  {
    use S_,
    finish,
  },
  cases foo with r2 bar,
  {
    use S_,
    finish,
  },
  cases bar with r3 r4;
  {
    use R_,
    finish,
  },
end


example : grammar_generates bezkontextova.to_grammar [a_, a_, b_, c_, c_, c_] :=
begin
  unfold bezkontextova,
  simp,
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
    use ((subtype.mk [S] (by { use S_, finish })), [a, S, c]),
    split,
    {
      finish,
    },
    use [[], []],
    simp,
  },
  {
    use ((subtype.mk [S] (by { use S_, finish })), [a, S, c]),
    split,
    {
      finish,
    },
    use [[a], [c]],
    simp,
  },
  {
    use ((subtype.mk [S] (by { use S_, finish })), [R]),
    split,
    {
      finish,
    },
    use [[a, a], [c, c]],
    simp,
  },
  {
    use ((subtype.mk [R] (by { use R_, finish })), [b, R, c]),
    split,
    {
      finish,
    },
    use [[a, a], [c, c]],
    simp,
  },
  {
    simp,
    use ((subtype.mk [R] (by { use R_, finish })), []),
    split,
    {
      finish,
    },
    use [[a, a, b], [c, c, c]],
    simp,
    finish,
  },
end

end demo
