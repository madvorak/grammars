import data.fintype.basic
import logic.relation
import computability.language
import context_free.cfg


inductive symbo (τ : Type) (ν : Type)
| terminal    : τ → symbo
| nonterminal : ν → symbo


section def_grammars
variables (T : Type) (N : Type)

structure grammar :=
(initial : N)
(rules : list (prod
  {str : list (symbo T N) // ∃ n : N, (symbo.nonterminal n) ∈ str}
  (list (symbo T N))
))

structure noncontracting extends grammar T N :=
(len_non_decr : 
  ∀ r : (prod
    {str : list (symbo T N) // ∃ n : N, (symbo.nonterminal n) ∈ str}
    (list (symbo T N))
  ), r ∈ rules → 
    (r.fst.val.length ≤ r.snd.length)
)

structure noncontracting_with_empty_word extends grammar T N :=
(len_non_decr_or_snd_empty : 
  ∀ r : (prod
    {str : list (symbo T N) // ∃ n : N, (symbo.nonterminal n) ∈ str}
    (list (symbo T N))
  ), r ∈ rules → or
    ((r.fst.val.length ≤ r.snd.length) ∧ (symbo.nonterminal initial ∉ r.snd))
    ((r.fst.val = [symbo.nonterminal initial]) ∧ (r.snd = []))
)

structure kuroda_normal_form extends noncontracting_with_empty_word T N :=
(kuroda_condition :
  ∀ r : (prod
    {str : list (symbo T N) // ∃ n : N, (symbo.nonterminal n) ∈ str}
    (list (symbo T N))
  ), r ∈ rules → (
    ∃ A B C D : N, and
      (r.fst.val = [symbo.nonterminal A, symbo.nonterminal B])
      (r.snd     = [symbo.nonterminal C, symbo.nonterminal D])
  ) ∨ (
    ∃ X Y Z : N, and
      (r.fst.val = [symbo.nonterminal X])
      (r.snd     = [symbo.nonterminal Y, symbo.nonterminal Z])
  ) ∨ (
    ∃ R : N, ∃ a : T, and
      (r.fst.val = [symbo.nonterminal R])
      (r.snd     = [symbo.terminal a])  
  ) ∨ (  
      (r.fst.val = [symbo.nonterminal initial]) ∧ (r.snd = [])
  )
)

structure context_free extends grammar T N :=
(fst_singleton_nonterminal :
  ∀ r : (prod
    {str : list (symbo T N) // ∃ n : N, (symbo.nonterminal n) ∈ str}
    (list (symbo T N))
  ), r ∈ rules → 
    (∃ n : N, r.fst.val = [symbo.nonterminal n])
)

structure left_linear extends context_free T N :=
(snd_max_one_nonterminal :
  ∀ r : (prod
    {str : list (symbo T N) // ∃ n : N, (symbo.nonterminal n) ∈ str}
    (list (symbo T N))
  ), r ∈ rules → 
    (∃ n : N, ∃ ts : list T, or
      (r.snd = list.map symbo.terminal ts)
      (r.snd = symbo.nonterminal n :: (list.map symbo.terminal ts))
    )
)

structure right_linear extends context_free T N :=
(snd_max_one_nonterminal :
  ∀ r : (prod
    {str : list (symbo T N) // ∃ n : N, (symbo.nonterminal n) ∈ str}
    (list (symbo T N))
  ), r ∈ rules → 
    (∃ ts : list T, ∃ n : N, or
      (r.snd = list.map symbo.terminal ts)
      (r.snd = (list.map symbo.terminal ts) ++ [symbo.nonterminal n])
    )
)

end def_grammars


section def_derivations
variables {T N : Type} (g : grammar T N)

def letter := symbo T N

def grammar_transforms (oldWord newWord : list letter) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbo T N),
  oldWord = (v ++ subtype.val (prod.fst r) ++ w) ∧ (newWord = v ++ (prod.snd r) ++ w)

def grammar_derives : list letter → list letter → Prop :=
relation.refl_trans_gen (grammar_transforms g)

def grammar_generates_str (str : list letter) : Prop :=
grammar_derives g [symbo.nonterminal g.initial] str

def grammar_generates (word : list T) : Prop :=
grammar_generates_str g (list.map symbo.terminal word)

def grammar_language : language T :=
grammar_generates g

end def_derivations



section demo

def a_ : fin 3 := 0
def a : symbo (fin 3) (fin 2) := symbo.terminal a_

def b_ : fin 3 := 1
def b : symbo (fin 3) (fin 2) := symbo.terminal b_

def c_ : fin 3 := 2
def c : symbo (fin 3) (fin 2) := symbo.terminal c_

def S_ : fin 2 := 0
def S : symbo (fin 3) (fin 2) := symbo.nonterminal S_

def R_ : fin 2 := 1
def R : symbo (fin 3) (fin 2) := symbo.nonterminal R_

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


example {T : Type} (L : language T) :
  is_CF L →
    ∃ N : Type, ∃ g : context_free T N,
      grammar_generates (g.to_grammar) = L :=
begin
  rintro ⟨ g₀, ass ⟩,
  use g₀.nt,
  let g' : grammar T g₀.nt := grammar.mk g₀.initial (list.map (
    λ r : g₀.nt × (list (symbol T g₀.nt)),
      (⟨[symbo.nonterminal r.fst], (by { use r.fst, apply list.mem_cons_self, })⟩, list.map (
        λ s : symbol T g₀.nt, match s with
          | (symbol.terminal ter) := symbo.terminal ter
          | (symbol.nonterminal nonter) := symbo.nonterminal nonter
        end
      ) r.snd))
    g₀.rules),
  use context_free.mk g' (by {
    intros r h,
    simp at h,
    rcases h with ⟨ a, b, in_g₀, eq_r ⟩,
    rw ← eq_r,
    simp,
  }),
  rw ← ass,

  unfold CF_language,
  simp,
  ext1,
  unfold grammar_generates,
  unfold CF_generates,
  unfold grammar_generates_str,
  unfold CF_generates_str,
  sorry,
end
