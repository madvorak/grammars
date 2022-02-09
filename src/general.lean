import logic.relation
import data.fintype.basic
import computability.language


inductive symbol (τ : Type) (ν : Type) [fintype τ] [fintype ν]
| terminal    : τ → symbol
| nonterminal : ν → symbol


section def_grammars
variables (T : Type) (N : Type) [fintype T] [fintype N]

structure grammar :=
(initial : N)
(rules : list (prod
  {str : list (symbol T N) // ∃ t : T, (symbol.terminal t) ∈ str}
  (list (symbol T N))
))

structure noncontracting extends grammar T N :=
(len_non_decr : 
  ∀ r : (prod
    {str : list (symbol T N) // ∃ t : T, (symbol.terminal t) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → 
    (r.fst.val.length ≤ r.snd.length)
)

structure noncontracting_with_empty_word extends grammar T N :=
(len_non_decr_or_yields_empty : 
  ∀ r : (prod
    {str : list (symbol T N) // ∃ t : T, (symbol.terminal t) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → or
    ((r.fst.val.length ≤ r.snd.length) ∧ (symbol.nonterminal initial ∉ r.snd))
    ((r.fst.val = [symbol.nonterminal initial]) ∧ (r.snd = []))
)

structure context_free extends grammar T N :=
(left_one_nonterminal :
  ∀ r : (prod
    {str : list (symbol T N) // ∃ t : T, (symbol.terminal t) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → 
    (∃ n : N, r.fst.val = [symbol.nonterminal n])
)

structure right_linear extends context_free T N :=
(right_one_terminal :
  ∀ r : (prod
    {str : list (symbol T N) // ∃ t : T, (symbol.terminal t) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → 
    (∃ n : N, ∃ ts : list T, or
      (r.snd = list.map symbol.terminal ts)
      (r.snd = symbol.nonterminal n :: (list.map symbol.terminal ts))
    )
)

structure left_linear extends context_free T N :=
(right_one_terminal :
  ∀ r : (prod
    {str : list (symbol T N) // ∃ t : T, (symbol.terminal t) ∈ str}
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
  oldWord = v ++ (subtype.val (prod.fst r)) ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def grammar_derives : list letter → list letter → Prop := 
relation.refl_trans_gen (grammar_transforms g)

def grammar_generates_str (str : list letter) : Prop :=
grammar_derives g [symbol.nonterminal g.initial] str

def grammar_generates (word : list T) : Prop :=
grammar_generates_str g (list.map symbol.terminal word)

def grammar_language : language T :=
grammar_generates g

end def_derivations
