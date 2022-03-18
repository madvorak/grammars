import context_free.cfg


section def_grammars
variables (T : Type) (N : Type)

structure general_grammar :=
(initial : N)
(rules : list (prod
  {str : list (symbol T N) // ∃ n : N, (symbol.nonterminal n) ∈ str}
  (list (symbol T N))
))

structure noncontracting extends general_grammar T N :=
(len_non_decr : 
  ∀ r : (prod
    {str : list (symbol T N) // ∃ n : N, (symbol.nonterminal n) ∈ str}
    (list (symbol T N))
  ), r ∈ rules → 
    (r.fst.val.length ≤ r.snd.length)
)

structure noncontracting_with_empty_word extends general_grammar T N :=
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

structure context_free extends general_grammar T N :=
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
variables {T N : Type} (g : general_grammar T N)

def letter := symbol T N

def general_grammar_transforms (oldWord newWord : list letter) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbol T N),
  oldWord = (v ++ subtype.val (prod.fst r) ++ w) ∧ (newWord = v ++ (prod.snd r) ++ w)

def general_grammar_derives : list letter → list letter → Prop :=
relation.refl_trans_gen (general_grammar_transforms g)

def general_grammar_generates_str (str : list letter) : Prop :=
general_grammar_derives g [symbol.nonterminal g.initial] str

def general_grammar_generates (word : list T) : Prop :=
general_grammar_generates_str g (list.map symbol.terminal word)

def general_grammar_language : language T :=
general_grammar_generates g

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

def gramatika : general_grammar (fin 3) (fin 2) := general_grammar.mk S_ [
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


example : general_grammar_generates bezkontextova.to_general_grammar [a_, a_, b_, c_, c_, c_] :=
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


section CF_equivalences

lemma equivalence_of_CF_formalisms {T : Type} (L : language T) :
  is_CF L →
    ∃ N : Type, ∃ g : context_free T N,
      general_grammar_generates (g.to_general_grammar) = L :=
begin
  rintro ⟨ g₀, ass ⟩,
  use g₀.nt,
  let g' : general_grammar T g₀.nt := general_grammar.mk g₀.initial (list.map (
    λ r : g₀.nt × (list (symbol T g₀.nt)),
      (⟨[symbol.nonterminal r.fst], (by { use r.fst, apply list.mem_cons_self, })⟩, r.snd))
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
  unfold general_grammar_generates,
  unfold CF_generates,
  unfold general_grammar_generates_str,
  unfold CF_generates_str,
  ext1,
  split,
  {
    have deri_of_deri : ∀ w : list letter,
        general_grammar_derives g' [symbol.nonterminal g'.initial] w →
          CF_derives g₀ [symbol.nonterminal g₀.initial] w,
    {
      intros w h,
      induction h with y z trash orig ih,
      {
        exact CF_deri_self,
      },
      apply CF_deri_of_deri_tran,
      {
        exact ih,
      },
      rcases orig with ⟨ rule, rule_in, u, v, befo, afte ⟩,
      rw list.mem_map at rule_in,
      rcases rule_in with ⟨ the_rule, the_in, eq_the ⟩,
      use the_rule,
      split,
      {
        exact the_in,
      },
      use u,
      use v,
      split,
      {
        rw ← eq_the at befo,
        dsimp at befo,
        exact befo,
      },
      {
        rw ← eq_the at afte,
        dsimp at afte,
        exact afte,
      },
    },
    exact deri_of_deri (list.map symbol.terminal x),
  },
  {
    have deri_of_deri : ∀ w : list letter,
        CF_derives g₀ [symbol.nonterminal g₀.initial] w →
          general_grammar_derives g' [symbol.nonterminal g'.initial] w,
    {
      intros w h,
      induction h with y z trash orig ih,
      {
        exact relation.refl_trans_gen.refl,
      },
      fconstructor,
      use y,
      {
        exact ih,
      },
      rcases orig with ⟨ rule, rule_in, u, v, befo, afte ⟩,
      unfold general_grammar_transforms,
      use (⟨[symbol.nonterminal rule.fst], (by { use rule.fst, apply list.mem_cons_self, })⟩, rule.snd),
      split,
      {
        finish,
      },
      use u,
      use v,
      split,
      {
        rw befo,
      },
      {
        rw afte,
      },
    },
    exact deri_of_deri (list.map symbol.terminal x),
  },
end

end CF_equivalences
