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

end cfg_derivations


section cfg_cfl
variable {T : Type}

def CF_language (g : CF_grammar T) : language T :=
CF_generates g

def is_CF (L : language T) :=
∃ g : CF_grammar T, CF_language g = L

end cfg_cfl


section cfg_utilities
variables {T : Type} {g : CF_grammar T}

lemma CF_derives_reflexive {w : list (symbol T g.nt)} :
  CF_derives g w w :=
relation.refl_trans_gen.refl

lemma CF_derives_transitive {u w : list (symbol T g.nt)} (v : list (symbol T g.nt))
  (huv : CF_derives g u v) (hvw : CF_derives g v w) :
    CF_derives g u w :=
relation.refl_trans_gen.trans huv hvw

lemma CF_der_of_der_tra {u w : list (symbol T g.nt)} (v : list (symbol T g.nt))
  (huv : CF_derives g u v) (hvw : CF_transforms g v w) :
    CF_derives g u w :=
CF_derives_transitive v huv (relation.refl_trans_gen.single hvw)

lemma CF_der_of_tra_der {u w : list (symbol T g.nt)} (v : list (symbol T g.nt))
  (huv : CF_transforms g u v) (hvw : CF_derives g v w) :
    CF_derives g u w :=
CF_derives_transitive v (relation.refl_trans_gen.single huv) hvw

lemma CF_derives_with_prefix {oldWord newWord : list (symbol T g.nt)}
  (prefi : list (symbol T g.nt)) (h : CF_derives g oldWord newWord) :
    CF_derives g (prefi ++ oldWord) (prefi ++ newWord) :=
begin
  induction h with a b irr hyp ih,
  {
    apply CF_derives_reflexive,
  },
  apply CF_der_of_der_tra (prefi ++ a),
  {
    exact ih,
  },

  cases hyp with rule foo,
  cases foo with rule_in bar,
  cases bar with v baz,
  cases baz with w ass,
  cases ass with h_bef h_aft,
  use rule,
  split,
  {
    exact rule_in,
  },

  use prefi ++ v,
  use w,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma CF_derives_with_postfix {oldWord newWord : list (symbol T g.nt)}
  (posfi : list (symbol T g.nt)) (h : CF_derives g oldWord newWord) :
    CF_derives g (oldWord ++ posfi) (newWord ++ posfi) :=
begin
  induction h with a b irr hyp ih,
  {
    apply CF_derives_reflexive,
  },
  apply CF_der_of_der_tra (a ++ posfi),
  {
    exact ih,
  },

  cases hyp with rule foo,
  cases foo with rule_in bar,
  cases bar with v baz,
  cases baz with w ass,
  cases ass with h_bef h_aft,
  use rule,
  split,
  {
    exact rule_in,
  },

  use v,
  use w ++ posfi,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma CF_derives_with_prefix_and_postfix {oldWord newWord : list (symbol T g.nt)}
  (prefi posfi : list (symbol T g.nt)) (h : CF_derives g oldWord newWord) :
    CF_derives g (prefi ++ oldWord ++ posfi) (prefi ++ newWord ++ posfi) :=
begin
  apply CF_derives_with_postfix,
  apply CF_derives_with_prefix,
  exact h,
end

end cfg_utilities


section cfg_demonstrations

private def a_ : fin 3 := 0
private def a : symbol (fin 3) (fin 2) := symbol.terminal a_

private def b_ : fin 3 := 1
private def b : symbol (fin 3) (fin 2) := symbol.terminal b_

private def c_ : fin 3 := 2
private def c : symbol (fin 3) (fin 2) := symbol.terminal c_

private def S_ : fin 2 := 0
private def S : symbol (fin 3) (fin 2) := symbol.nonterminal S_

private def R_ : fin 2 := 1
private def R : symbol (fin 3) (fin 2) := symbol.nonterminal R_

private def gramatika : CF_grammar (fin 3) :=
CF_grammar.mk (fin 2) S_ [
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


private def anbmcnm (n m : ℕ) : list (fin 3) :=
(list.repeat a_ n) ++ (list.repeat b_ m) ++ (list.repeat c_ (n+m))

private def language_abc : language (fin 3) :=
λ x, ∃ n m : ℕ, x = anbmcnm n m

example : [a_, a_, b_, c_, c_, c_] ∈ language_abc :=
begin
  use 2,
  use 1,
  refl,
end

example : CF_language gramatika = language_abc :=
begin
  ext,

  split,
  {
    -- prove `x ∈ CF_language gramatika → x ∈ language_abc` here
    sorry,
  },
  {
    intro h,
    cases h with n hy,
    cases hy with m hyp,
    rw hyp,

    have epoch_a : ∀ i : ℕ, CF_derives gramatika [S] ((list.repeat a i) ++ [S] ++ (list.repeat c i)),
    {
      intro i,
      induction i with n' ih,
      {
        apply CF_derives_reflexive,
      },
      apply CF_der_of_der_tra _ ih,

      use (S_, [a, S, c]),
      split,
      {
        apply list.mem_cons_self,
      },
      use (list.repeat a n'),
      use (list.repeat c n'),
      split,
      {
        refl,
      },
      simp,
      change list.repeat a (n' + 1) ++ S :: c :: list.repeat c n' = list.repeat a n' ++ a :: S :: c :: list.repeat c n',
      simp [list.repeat_add, list.append_assoc],
    },
    have epoch_b : ∀ i : ℕ, CF_derives gramatika [R] ((list.repeat b i) ++ [R] ++ (list.repeat c i)),
    {
      intro j,
      induction j with m' jh,
      {
        apply CF_derives_reflexive,
      },
      apply CF_der_of_der_tra _ jh,

      use (R_, [b, R, c]),
      split,
      {
        apply list.mem_cons_of_mem,
        apply list.mem_cons_of_mem,
        apply list.mem_cons_self,
      },
      use (list.repeat b m'),
      use (list.repeat c m'),
      split,
      {
        refl,
      },
      simp,
      change list.repeat b (m' + 1) ++ R :: c :: list.repeat c m' = list.repeat b m' ++ b :: R :: c :: list.repeat c m',
      simp [list.repeat_add, list.append_assoc],
    },

    fconstructor,
      exact (list.repeat a n) ++ (list.repeat b m) ++ [R] ++ (list.repeat c (n+m)),
    {
      have middle_step : CF_derives gramatika
        ((list.repeat a n) ++ [S] ++ (list.repeat c n))
        ((list.repeat a n) ++ [R] ++ (list.repeat c n)),
      {
        fconstructor,
          exact ((list.repeat a n) ++ [S] ++ (list.repeat c n)),
        {
          refl,
        },
        use (S_, [R]),
        split,
        {
          apply list.mem_cons_of_mem,
          apply list.mem_cons_self,
        },
        use (list.repeat a n),
        use (list.repeat c n),
        split;
        refl,
      },
      apply CF_derives_transitive,
      {
        specialize epoch_a n,
        finish,
      },
      apply CF_derives_transitive,
      {
        finish,
      },
      change CF_derives gramatika (list.repeat a n ++ ([R] ++ list.repeat c n)) (list.repeat a n ++ list.repeat b m ++ [R] ++ list.repeat c (n + m)),
      rw ← list.append_assoc,
      have cnm : list.repeat c (n + m) = list.repeat c m ++ list.repeat c n,
      {
        rw add_comm,
        apply list.repeat_add,
      },
      rw cnm,
      have rebra : (list.repeat a n ++ list.repeat b m ++ [R] ++ (list.repeat c m ++ list.repeat c n)) = (list.repeat a n ++ (list.repeat b m ++ [R] ++ list.repeat c m) ++ list.repeat c n),
      {
        simp only [list.append_assoc],
      },
      rw rebra,
      apply CF_derives_with_prefix_and_postfix,
      exact epoch_b m,
    },
    use (R_, []),
    split,
    {
      apply list.mem_cons_of_mem,
      apply list.mem_cons_of_mem,
      apply list.mem_cons_of_mem,
      apply list.mem_cons_self,
    },
    use (list.repeat a n ++ list.repeat b m),
    use list.repeat c (n + m),
    split,
    {
      refl,
    },
    simp,
    unfold anbmcnm,
    simp,
    refl,
  },
end

end cfg_demonstrations
