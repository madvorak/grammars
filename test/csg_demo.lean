import context_sensitive.csg
import tactic


inductive Te
| a_ : Te
| b_ : Te
| c_ : Te

inductive Nt
| B_ : Nt
| C_ : Nt
| R_ : Nt
| S_ : Nt
| X_ : Nt
| Y_ : Nt
| Z_ : Nt

private def a : symbol Te Nt := symbol.terminal Te.a_
private def b : symbol Te Nt := symbol.terminal Te.b_
private def c : symbol Te Nt := symbol.terminal Te.c_

private def B : symbol Te Nt := symbol.nonterminal Nt.B_
private def C : symbol Te Nt := symbol.nonterminal Nt.C_
private def R : symbol Te Nt := symbol.nonterminal Nt.R_
private def S : symbol Te Nt := symbol.nonterminal Nt.S_
private def X : symbol Te Nt := symbol.nonterminal Nt.X_
private def Y : symbol Te Nt := symbol.nonterminal Nt.Y_
private def Z : symbol Te Nt := symbol.nonterminal Nt.Z_


/-- rule `S → aSBC | aRC` as two context-sensitive rules -/
private def r₁ : csrule Te Nt := csrule.mk [] Nt.S_ [] [a, S, B, C]
private def r₂ : csrule Te Nt := csrule.mk [] Nt.S_ [] [a, R, C]

/-- non-contracting rule `CB → BC` modelled by `CB → XB → XC → BC` which is context-sensitive -/
private def r₃  : csrule Te Nt := csrule.mk [] Nt.C_ [B] [X]
private def r₃' : csrule Te Nt := csrule.mk [X] Nt.B_ [] [C]
private def r₃'': csrule Te Nt := csrule.mk [] Nt.X_ [C] [B]

/-- non-contracting rule `RB → bR` modelled by `RB → YB → YR → bR` which is context-sensitive -/
private def r₄  : csrule Te Nt := csrule.mk [] Nt.R_ [B] [Y]
private def r₄' : csrule Te Nt := csrule.mk [Y] Nt.B_ [] [R]
private def r₄'': csrule Te Nt := csrule.mk [] Nt.Y_ [R] [b]

/-- non-contracting rule `RC → bc` modelled by `RC → ZC → Zc → bc` which is context-sensitive -/
private def r₅  : csrule Te Nt := csrule.mk [] Nt.R_ [C] [Z]
private def r₅' : csrule Te Nt := csrule.mk [Z] Nt.C_ [] [c]
private def r₅'': csrule Te Nt := csrule.mk [] Nt.Z_ [c] [b]

/-- context-sensitive rule `cC → cc` -/
private def r₆ : csrule Te Nt := csrule.mk [c] Nt.C_ [] [c]


private def gramatika : CS_grammar Te :=
CS_grammar.mk Nt Nt.S_ [r₁, r₂, r₃, r₃', r₃'', r₄, r₄', r₄'', r₅, r₅', r₅'', r₆]

/-- generate `abc` by the grammar above -/
example : [Te.a_, Te.b_, Te.c_] ∈ CS_language gramatika :=
begin
  unfold gramatika,

  apply CS_deri_of_tran_deri,
  {
    use r₂,
    split,
    {
      finish,
    },
    use [[], []],
    split;
    refl,
  },

  apply CS_deri_of_tran_deri,
  {
    use r₅,
    split,
    {
      finish,
    },
    use [[a], []],
    split;
    refl,
  },

  apply CS_deri_of_tran_deri,
  {
    use r₅',
    split,
    {
      finish,
    },
    use [[a], []],
    split;
    refl,
  },

  apply CS_deri_of_tran,
  {
    use r₅'',
    split,
    {
      finish,
    },
    use [[a], []],
    split;
    refl,
  },
end

private meta def CS_step : tactic unit :=
 `[ 
    apply CS_deri_of_tran_deri, use p.1, split,
    simp only [ list.mem_cons_iff, eq_self_iff_true, true_or, or_true ],
    use p.2.1, use p.2.2, split; refl
  ]

private def empt : list (symbol Te Nt) := []

/-- generate `aabbcc` by the grammar above -/
example : [Te.a_, Te.a_, Te.b_, Te.b_, Te.c_, Te.c_] ∈ CS_language gramatika :=
begin
  unfold gramatika,

  let p := (r₁, empt, empt),
  CS_step,

  let p := (r₂, [a], [B, C]),
  CS_step,

  let p := (r₃  , [a, a, R], [C]),
  CS_step,
  let p := (r₃' , [a, a, R], [C]),
  CS_step,
  let p := (r₃'', [a, a, R], [C]),
  CS_step,

  let p := (r₄  , [a, a], [C, C]),
  CS_step,
  let p := (r₄' , [a, a], [C, C]),
  CS_step,
  let p := (r₄'', [a, a], [C, C]),
  CS_step,

  let p := (r₅  , [a, a, b], [C]),
  CS_step,
  let p := (r₅' , [a, a, b], [C]),
  CS_step,
  let p := (r₅'', [a, a, b], [C]),
  CS_step,

  let p := (r₆, [a, a, b, b], empt),
  CS_step,

  apply CS_deri_self,
end

/-- generate `aaabbbccc` by the grammar above -/
example : [Te.a_, Te.a_, Te.a_, Te.b_, Te.b_, Te.b_, Te.c_, Te.c_, Te.c_] ∈ CS_language gramatika :=
begin
  unfold CS_language,
  change CS_derives gramatika [symbol.nonterminal Nt.S_] [a, a, a, b, b, b, c, c, c],
  

  sorry,
end
