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

def CF_transforms (gr : CF_grammar) (oldWord newWord : list symbol) : Prop :=
∃ r ∈ gr.rules, ∃ v w : list symbol, 
  oldWord = v ++ [subtype.val (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def CF_derives (gr : CF_grammar) := relation.refl_trans_gen (CF_transforms gr)

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

example : CF_transforms gramatika [b, S, b, a] [b, a, S, c, b, a] :=
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
  have step_1 : CF_transforms gramatika [S] [a, S, c],
  {
    unfold gramatika,
    use (S, [a, S, c]),
    simp,
    use [[],[]],
    finish,
  },
  have step_2 : CF_transforms gramatika [a, S, c] [a, T, c],
  {
    unfold gramatika,
    use (S, [T]),
    simp,
    use [[a], [c]],
    finish,
  },
  have step_3 : CF_transforms gramatika [a, T, c] [a, c],
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

example : ¬ CF_transforms gramatika [S, a, a, b, b] [c, c, c] :=
begin
  have necessary_suffix: ∀ u v : list symbol, ∀ x : symbol, 
    (CF_transforms gramatika [S, a, a, b, b] v    ∧
       v = u ++ [x]) → 
        x = b,
  {
    unfold gramatika,
    intros u v x h,
    cases h with h_transf h_concat,
    cases h_transf with usedrule hy,
    cases hy with belongs foo,
    cases foo with preffii bar,
    cases bar with suffii hypot,
    rw h_concat at hypot,
    cases hypot with presubst postsubst,
    have nonempty: list.length suffii > 0,
    {
      have cannotbb: usedrule.fst.val ≠ b,
      {
        finish,
      },
      by_contradiction,
      have hn: suffii.length = 0,
      {
        finish,
      },
      have wosuffii: [↑S, ↑a, ↑a, ↑b, ↑b] = preffii ++ [usedrule.fst.val],
      {
        have hempty: suffii = [],
        {
          rw list.length_eq_zero at hn,
          exact hn,
        },
        finish,
      },
      have deconcanat: [↑S, ↑a, ↑a, ↑b, ↑b] = [↑S, ↑a, ↑a, ↑b] ++ [↑b],
      {
        simp,
      },
      have lastlemma: [↑b] = [usedrule.fst.val],
      {
        rw deconcanat at wosuffii,
        exact list.append_inj_right' wosuffii (by refl),
      },
      finish,
    },
    have ending: ∃ w : list symbol, suffii = w ++ [b],
    {
      cases classical.em ((list.length suffii) = 0),
      {
        rw h at nonempty,
        exfalso,
        exact false_of_ne (ne_of_gt nonempty),
      },
      have h1: suffii.length ≥ 1,
      {
        linarith,
      },
      /-
      presubst: [↑S, ↑a, ↑a, ↑b, ↑b] = preffii ++ [usedrule.fst.val] ++ suffii
      h1: suffii.length ≥ 1
      ⊢ ∃ (w : list symbol), suffii = w ++ [↑b]
      -/
      have splitt: ∃ w' : list symbol, ∃ x' : symbol, suffii = w' ++ [x'],
      {
        use list.take ((list.length suffii) - 1) suffii,
        cases list.nth suffii ((list.length suffii) - 1),
        {
          sorry,
        },
        use val,
        sorry,
      },
      cases splitt with w' foo,
      cases foo with x' splitted,
      rw splitted at presubst,
      have rearrang: [↑S, ↑a, ↑a, ↑b, ↑b] = (preffii ++ [usedrule.fst.val] ++ w') ++ [x'],
      {
        simp only [list.append_assoc],
        finish,
      },
      have chopped: [↑S, ↑a, ↑a, ↑b] ++ [↑b] = (preffii ++ [usedrule.fst.val] ++ w') ++ [x'],
      {
        finish,
      },
      have almostthere: [↑b] = [x'],
      {
        exact list.append_inj_right' chopped (by refl),
      },
      rw splitted,
      use w',
      rw almostthere,
    },
    cases ending with w lastchar,
    rw lastchar at postsubst,
    have rearranged: u ++ [x] = (preffii ++ usedrule.snd ++ w) ++ [b],
    {
      simp only [list.append_assoc],
      finish,
    },
    have lastone: [x] = [b],
    {
      exact list.append_inj_right' rearranged (by refl),
    },
    finish,
  },
  intro hyp,
  specialize necessary_suffix [c, c] [c, c, c] c,
  have conj: CF_transforms gramatika [↑S, ↑a, ↑a, ↑b, ↑b] [↑c, ↑c, ↑c] ∧
                                    [↑c, ↑c, ↑c] = [↑c, ↑c] ++ [↑c],
  {
    split,
    exact hyp,
    finish,
  },
  specialize necessary_suffix conj,
  finish,
end

example : ¬ CF_transforms gramatika [b, S, b, a] [b, S, c, b, a] :=
begin
  sorry,
end

example : ¬ CF_transforms gramatika [b, S, b, a] [b, b, S, c, b, a] :=
begin
  sorry,
end
