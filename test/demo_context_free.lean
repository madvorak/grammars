import classes.context_free.basics.toolbox
import utilities.list_utils
import utilities.written_by_others.trim_assoc


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

private def gr_add : CF_grammar (fin 3) :=
CF_grammar.mk (fin 2) S_ [
  (S_, [a, S, c]),
  (S_, [R]),
  (R_, [b, R, c]),
  (R_, [])
]

example : CF_generates gr_add [a_, a_, b_, c_, c_, c_] :=
begin
  unfold gr_add,

  apply CF_deri_of_tran_deri,
  {
    use (S_, [a, S, c]),
    split_ile,
    use [[], []],
    simp,
  },

  apply CF_deri_of_tran_deri,
  {
    use (S_, [a, S, c]),
    split_ile,
    use [[a], [c]],
    rw S,
    simp,
  },

  apply CF_deri_of_tran_deri,
  {
    use (S_, [R]),
    split_ile,
    use [[a, a], [c, c]],
    simp,
  },

  apply CF_deri_of_tran_deri,
  {
    use (R_, [b, R, c]),
    split_ile,
    use [[a, a], [c, c]],
    rw R,
    simp,
  },

  apply CF_deri_of_tran,
  {
    use (R_, []),
    split_ile,
    use [[a, a, b], [c, c, c]],
    repeat { try {split}, try {refl} },
  },
end


private def anbmcnm (n m : ℕ) : list (fin 3) :=
list.replicate n a_ ++ list.replicate m b_ ++ list.replicate (n + m) c_

private def language_add : language (fin 3) :=
λ x, ∃ n m : ℕ, x = anbmcnm n m

example : [a_, a_, b_, c_, c_, c_] ∈ language_add :=
begin
  use 2,
  use 1,
  refl,
end

example : CF_language gr_add = language_add :=
begin
  ext,

  split,
  {
    -- prove `x ∈ CF_language gr_add → x ∈ language_add` here
    intro ass,
    change CF_derives gr_add [S] (list.map symbol.terminal x) at ass,

    have possib : ∀ w : list (symbol (fin 3) gr_add.nt),
      CF_derives gr_add [S] w →
        (∃ i : ℕ, w = list.replicate i a ++ [S] ++ list.replicate i c) ∨
        (∃ i j : ℕ, w = list.replicate i a ++ list.replicate j b ++ [R] ++ list.replicate (i + j) c) ∨
        (∃ i j : ℕ, w = list.replicate i a ++ list.replicate j b ++ list.replicate (i + j) c),
    {
      intros w h,
      induction h with y z irr step ih,
      {
        left,
        use 0,
        refl,
      },
      cases step with rule foo,
      cases foo with rule_in bar,
      cases bar with u baz,
      cases baz with v hyp,
      cases hyp with hyp_bef hyp_aft,

      cases ih with case₁ caseᵣ,
      {
        cases rule_in,
        {
          left,
          cases case₁ with i the_case,
          rw list.append_assoc at the_case,
          use i + 1,
          have almost : z = list.replicate i a ++ [a, S, c] ++ list.replicate i c,
          {
            rw hyp_bef at the_case,
            rw hyp_aft,
            rw rule_in at *,
            have u_must : u = list.replicate i a,
            {
              dsimp only at *,
              rw ←S at *,
              have indexS: (u ++ [S] ++ v).nth u.length = some S,
              {
                rw list.append_assoc,
                rw list.nth_append_right (le_of_eq rfl),
                rw tsub_self,
                refl,
              },
              cases @trichotomous ℕ (<) _ (list.length u) i with hlt hge,
              {
                exfalso,
                rw the_case at indexS,
                rw ←list.nth_take hlt at indexS,
                rw list.take_append_of_le_length (le_of_eq (list.length_replicate i a).symm) at indexS,
                rw list.take_replicate at indexS,
                rw min_self at indexS,
                rw ←list.length_replicate i a at hlt,
                have please : (list.replicate i a).nth_le u.length hlt = S,
                {
                  rw list.nth_le_nth hlt at indexS,
                  injection indexS,
                },
                rw list.nth_le_replicate a hlt at please,
                injection please,
              },
              cases hge.symm with hgt heq,
              {
                exfalso,
                rw the_case at indexS,
                have rightend : u.length < (list.replicate i a ++ [S] ++ list.replicate i c).length,
                {
                  have thelength := congr_arg list.length the_case,
                  rw list.append_assoc at thelength,
                  rw list.length_append at thelength,
                  rw list.append_assoc,
                  rw ←thelength,
                  rw list.length_append,
                  rw list.length_singleton,
                  rw ←add_assoc,
                  apply lt_of_lt_of_le,
                  {
                    exact lt_add_one u.length,
                  },
                  exact le_self_add,
                },
                rw ←list.append_assoc at indexS,
                rw list.nth_le_nth rightend at indexS,
                injection indexS with continue,
                have mala : (list.replicate i a ++ [S]).length ≤ u.length,
                {
                  rw list.length_append,
                  rw list.length_singleton,
                  rw list.length_replicate i a,
                  rw ←nat.succ_le_iff at hgt,
                  apply hgt,
                },
                rw list.nth_le_append_right mala at continue,
                finish,
              },
              rw list.append_assoc at the_case,
              apply list.append_inj_left the_case,
              rw heq,
              finish,
            },
            have v_must : v = list.replicate i c,
            {
              rw u_must at the_case,
              rw list.append_assoc at the_case,
              rw list.append_right_inj (list.replicate i a) at the_case,
              rw ←S at the_case,
              rw list.append_right_inj [S] at the_case,
              exact the_case,
            },
            rw u_must,
            rw v_must,
          },
          rw list.replicate_add,
          change z = list.replicate i a ++ [a] ++ [S] ++ list.replicate (i + 1) c,
          rw add_comm,
          rw list.replicate_add,
          change z = list.replicate i a ++ [a] ++ [S] ++ ([c] ++ list.replicate i c),
          rw ←list.append_assoc,
          rw list.append_assoc (list.replicate i a) [a],
          rw list.append_assoc (list.replicate i a) ([a] ++ [S]),
          convert almost,
        },
        cases rule_in,
        {
          right,
          left,
          cases case₁ with i the_case,
          use i,
          use 0,
          simp,
          have u_must : u = list.replicate i a,
          {
            have indexS: (u ++ [S] ++ v).nth u.length = some S,
            {
              rw list.append_assoc,
              rw list.nth_append_right (le_of_eq rfl),
              rw tsub_self,
              refl,
            },
            cases @trichotomous ℕ (<) _ (list.length u) i with hlt hge,
            {
              exfalso,
              rw hyp_bef at the_case,
              rw rule_in at *,
              rw ←list.nth_take hlt at indexS,
              simp at the_case,
              change u ++ ([S] ++ v) = list.replicate i a ++ ([S] ++ list.replicate i c) at the_case,
              rw list.append_assoc at indexS,
              rw the_case at indexS,
              rw list.take_append_of_le_length (le_of_eq (list.length_replicate i a).symm) at indexS,
              rw list.take_replicate at indexS,
              rw min_self at indexS,
              rw ←list.length_replicate i a at hlt,
              have please : (list.replicate i a).nth_le u.length hlt = S,
              {
                rw list.nth_le_nth hlt at indexS,
                injection indexS,
              },
              rw list.nth_le_replicate a hlt at please,
              injection please,
            },
            cases hge.symm with hgt heq,
            {
              exfalso,
              rw list.append_assoc at the_case,
              rw hyp_bef at the_case,
              rw rule_in at *,
              change u ++ [S] ++ v = list.replicate i a ++ S :: list.replicate i c at the_case,
              rw the_case at indexS,
              have rightend : u.length < (list.replicate i a ++ [S] ++ list.replicate i c).length,
              {
                have thelength := congr_arg list.length the_case,
                rw list.append_assoc at thelength,
                rw list.length_append at thelength,
                rw list.append_assoc,
                change u.length < (list.replicate i a ++ S :: list.replicate i c).length,
                rw ←thelength,
                rw list.length_append,
                rw list.length_singleton,
                rw ←add_assoc,
                apply lt_of_lt_of_le,
                {
                  exact lt_add_one u.length,
                },
                exact le_self_add,
              },
              change (list.replicate i a ++ ([S] ++ list.replicate i c)).nth u.length = some S at indexS,
              rw ←list.append_assoc at indexS,
              rw list.nth_le_nth rightend at indexS,
              injection indexS with continue,
              have mala : (list.replicate i a ++ [S]).length ≤ u.length,
              {
                rw list.length_append,
                rw list.length_singleton,
                rw list.length_replicate i a,
                rw ←nat.succ_le_iff at hgt,
                apply hgt,
              },
              rw list.nth_le_append_right mala at continue,
              finish,
            },
            rw list.append_assoc at the_case,
            rw hyp_bef at the_case,
            rw list.append_assoc at the_case,
            apply list.append_inj_left the_case,
            rw heq,
            rw list.length_replicate i a,
          },
          have v_must : v = list.replicate i c,
          {
            rw list.append_assoc at the_case,
            rw hyp_bef at the_case,
            rw list.append_assoc at the_case,
            rw u_must at the_case,
            rw list.append_right_inj (list.replicate i a) at the_case,
            rw rule_in at the_case,
            change [S] ++ v = [S] ++ list.replicate i c at the_case,
            rw list.append_right_inj [S] at the_case,
            exact the_case,
          },
          rw hyp_aft,
          rw u_must,
          rw v_must,
          rw rule_in,
          simp,
        },
        cases rule_in,
        any_goals { try { cases rule_in },
          exfalso,
          rw rule_in at hyp_bef,
          simp at hyp_bef,
          cases case₁ with i the_case,
          rw the_case at hyp_bef,
          have contra := congr_arg (λ lis, R ∈ lis) hyp_bef,
          rw ←R at contra,
          simp at contra,
          cases contra,
          {
            rw list.mem_replicate at contra,
            have triv : R ≠ a,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
          cases contra,
          {
            injection contra with contr,
            injection contr with cont,
            simp at cont,
            exact cont,
          },
          {
            rw list.mem_replicate at contra,
            have triv : R ≠ c,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
        },
        exfalso,
        exact (list.mem_nil_iff rule).1 rule_in,
      },
      cases caseᵣ with case₂ case₃,
      {
        cases rule_in,
        any_goals { try { cases rule_in },
          exfalso,
          rw rule_in at hyp_bef,
          simp at hyp_bef,
          cases case₂ with i foo,
          cases foo with j y_eq,
          rw y_eq at hyp_bef,
          have contra := congr_arg (λ lis, S ∈ lis) hyp_bef,
          rw ←S at contra,
          simp at contra,
          cases contra,
          {
            rw list.mem_replicate at contra,
            have triv : S ≠ a,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
          cases contra,
          {
            rw list.mem_replicate at contra,
            have triv : S ≠ b,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
          cases contra,
          {
            injection contra with contr,
            injection contr with cont,
            simp at cont,
            exact cont,
          },
          {
            rw list.mem_replicate at contra,
            have triv : S ≠ c,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
        },

        cases rule_in,
        any_goals { try { cases rule_in },
          rw rule_in at *,
          simp at *,
          cases case₂ with i foo,
          cases foo with j y_form,
          rw y_form at hyp_bef,

          have indexR: (u ++ [R] ++ v).nth u.length = some R,
          {
            rw list.append_assoc,
            rw list.nth_append_right (le_of_eq rfl),
            rw tsub_self,
            refl,
          },
          have u_eq : u = list.replicate i a ++ list.replicate j b,
          {
            cases @trichotomous ℕ (<) _ u.length (i + j) with hlt rest,
            {
              exfalso,
              rw ←list.nth_take hlt at indexR,
              have h_len : u.length < (list.replicate i a ++ list.replicate j b).length,
              {
                rw list.length_append,
                rw list.length_replicate,
                rw list.length_replicate,
                exact hlt,
              },
              have propos : (list.replicate i a ++ list.replicate j b).nth_le u.length h_len = R,
              {
                change list.replicate i a ++ (list.replicate j b ++ R :: list.replicate (i + j) c) = u ++ ([R] ++ v) at hyp_bef,
                rw ←list.append_assoc u [R] v at hyp_bef,
                rw ←hyp_bef at indexR,
                rw ←list.append_assoc at indexR,
                have take_beg :
                  list.take (i + j) (list.replicate i a ++ list.replicate j b ++ R :: list.replicate (i + j) c) =
                  (list.replicate i a ++ list.replicate j b),
                {
                  have len_ij : (list.replicate i a ++ list.replicate j b).length = i + j,
                  {
                    rw list.length_append,
                    rw list.length_replicate,
                    rw list.length_replicate,
                  },
                  rw list.take_append_of_le_length (le_of_eq len_ij.symm),
                  rw list.take_all_of_le,
                  exact le_of_eq len_ij,
                },
                rw take_beg at indexR,
                rw list.nth_le_nth h_len at indexR,
                injection indexR,
              },
              have yes_R : R ∈ (list.replicate i a ++ list.replicate j b),
              {
                let positive := list.nth_le_mem (list.replicate i a ++ list.replicate j b) u.length h_len,
                rw propos at positive,
                exact positive,
              },
              have not_R : R ∉ (list.replicate i a ++ list.replicate j b),
              {
                rw list.mem_append,
                push_neg,
                split,
                {
                  have nidRa : R ≠ a,
                  {
                    apply symbol.no_confusion,
                  },
                  by_contradiction,
                  rw list.mem_replicate at h,
                  exact nidRa h.right,
                },
                {
                  have nidRb : R ≠ b,
                  {
                    apply symbol.no_confusion,
                  },
                  by_contradiction,
                  rw list.mem_replicate at h,
                  exact nidRb h.right,
                },
              },
              exact not_R yes_R,
            },
            cases rest.symm with hgt heq,
            {
              exfalso,
              have yes_Rc : R ∈ list.replicate (i + j) c,
              {
                change
                  list.replicate i a ++ (list.replicate j b ++ R :: list.replicate (i + j) c) = u ++ ([R] ++ v)
                  at hyp_bef,
                rw ←list.append_assoc u [R] v at hyp_bef,
                rw ←hyp_bef at indexR,
                rw ←list.append_assoc at indexR,
                change
                  (list.replicate i a ++ list.replicate j b ++ ([R] ++ list.replicate (i + j) c)).nth u.length = some R
                  at indexR,
                rw ←list.append_assoc at indexR,
                rw list.nth_append_right at indexR,
                {
                  simp at indexR,
                  have trouble_len : (u.length - (i + (j + 1))) < (list.replicate (i + j) c).length,
                  {
                    rw list.length_replicate,
                    have lengths_sum : u.length ≤ i + j + i + j,
                    {
                      let lengs := congr_arg list.length hyp_bef,
                      repeat {
                        rw list.length_append at lengs,
                      },
                      rw list.length_replicate at lengs,
                      rw list.length_replicate at lengs,
                      simp at lengs,
                      linarith,
                    },
                    linarith,
                  },
                  rw list.nth_le_nth trouble_len at indexR,
                  {
                    finish,
                  },
                },
                rw list.length_append,
                rw list.length_append,
                rw list.length_replicate,
                rw list.length_replicate,
                convert hgt,
              },
              have not_Rc : R ∉ list.replicate (i + j) c,
              {
                by_contradiction,
                rw list.mem_replicate at h,
                have nidRc : R ≠ c,
                {
                  apply symbol.no_confusion,
                },
                exact nidRc h.right,
              },
              exact not_Rc yes_Rc,
            },
            rw ←list.append_assoc at hyp_bef,
            have lenlen : (list.replicate i a ++ list.replicate j b).length = u.length,
            {
              rw list.length_append,
              rw list.length_replicate,
              rw list.length_replicate,
              exact heq.symm,
            },
            symmetry,
            exact list.append_inj_left hyp_bef lenlen,
          },
          have v_eq : v = list.replicate (i + j) c,
          {
            rw u_eq at hyp_bef,
            rw ←list.append_assoc at hyp_bef,
            rw list.append_right_inj (list.replicate i a ++ list.replicate j b) at hyp_bef,
            symmetry,
            exact list.tail_eq_of_cons_eq hyp_bef,
          },
          rw u_eq at hyp_aft,
          rw v_eq at hyp_aft,
          rw hyp_aft,
        },

        {
          right,
          left,
          use i,
          use j + 1,
          have bpp : list.replicate (j + 1) b = list.replicate j b ++ [b],
          {
            rw list.replicate_add j 1 b,
            refl,
          },
          have cpp : list.replicate (i + (j + 1)) c = [c] ++ list.replicate (i + j) c,
          {
            rw ←add_assoc,
            rw add_comm,
            rw list.replicate_add 1 (i + j) c,
            refl,
          },
          rw bpp,
          rw cpp,
          rw list.append_assoc,
          apply congr_arg (λ lis, list.replicate i a ++ lis),
          rw list.append_assoc,
          apply congr_arg (λ lis, list.replicate j b ++ lis),
          rw list.singleton_append,
          rw list.singleton_append,
        },

        cases rule_in,
        {
          right,
          right,
          use i,
          use j,
          rw list.append_assoc,
        },

        exfalso,
        exact (list.mem_nil_iff rule).1 rule_in,
      },
      {
        exfalso,
        rw hyp_bef at case₃,
        cases case₃ with i foo,
        cases foo with j the_case,
        have contra := congr_arg (λ lis, symbol.nonterminal rule.fst ∈ lis) the_case,
        simp at contra,
        cases contra,
        {
          have neq : symbol.nonterminal rule.fst ≠ a,
          {
            apply symbol.no_confusion,
          },
          rw list.mem_replicate at contra,
          apply neq,
          exact contra.right,
        },
        cases contra,
        {
          have neq : symbol.nonterminal rule.fst ≠ b,
          {
            apply symbol.no_confusion,
          },
          rw list.mem_replicate at contra,
          apply neq,
          exact contra.right,
        },
        {
          have neq : symbol.nonterminal rule.fst ≠ c,
          {
            apply symbol.no_confusion,
          },
          rw list.mem_replicate at contra,
          apply neq,
          exact contra.right,
        },
      },
    },

    specialize possib (list.map symbol.terminal x) ass,
    cases possib with imposs rest,
    {
      exfalso,
      cases imposs with i hyp,
      have contra := congr_arg (λ xs, S ∈ xs) hyp,
      simp at contra,
      finish,
    },
    cases rest with imposs' necess,
    {
      exfalso,
      cases imposs' with i rest,
      cases rest with j hyp,
      have contra := congr_arg (λ xs, R ∈ xs) hyp,
      simp at contra,
      finish,
    },
    cases necess with n foobar,
    use n,
    cases foobar with m keyprop,
    use m,
    unfold anbmcnm,
    unfold a b c at keyprop,
    rw ←list.map_replicate symbol.terminal n a_ at keyprop,
    rw ←list.map_replicate symbol.terminal m b_ at keyprop,
    rw ←list.map_replicate symbol.terminal (n + m) c_ at keyprop,
    rw ←list.map_append at keyprop,
    rw ←list.map_append at keyprop,

    ext1 k,
    have kprop := congr_fun (congr_arg list.nth keyprop) k,
    rw list.nth_map at kprop,
    rw list.nth_map at kprop,

    cases x.nth k,
    {
      cases (list.replicate n a_ ++ list.replicate m b_ ++ list.replicate (n + m) c_).nth k,
      {
        refl,
      },
      {
        exfalso,
        injection kprop,
      },
    },
    {
      cases (list.replicate n a_ ++ list.replicate m b_ ++ list.replicate (n + m) c_).nth k,
      {
        exfalso,
        injection kprop,
      },
      {
        injection kprop,
        injection h_1,
        rw h_2,
      },
    },
  },
  {
    -- prove `x ∈ CF_language gr_add ← x ∈ language_add` here
    rintro ⟨n, m, hyp⟩,
    rw hyp,
    have epoch_a : ∀ i : ℕ, CF_derives gr_add [S] ((list.replicate i a) ++ [S] ++ (list.replicate i c)),
    {
      intro i,
      induction i with n' ih,
      {
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran ih,

      use (S_, [a, S, c]),
      split_ile,
      use [list.replicate n' a, list.replicate n' c],
      split,
      {
        refl,
      },
      rw [
        list.replicate_succ_eq_append_singleton a,
        list.replicate_succ_eq_singleton_append c,
        list.append_assoc,
        list.append_assoc,
        ←list.append_assoc [S],
        ←list.append_assoc [a],
        ←list.append_assoc (list.replicate n' a)
      ],
      refl,
    },
    have epoch_b : ∀ j : ℕ, CF_derives gr_add [R] ((list.replicate j b) ++ [R] ++ (list.replicate j c)),
    {
      intro j,
      induction j with m' jh,
      {
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran jh,

      use (R_, [b, R, c]),
      split_ile,
      use [list.replicate m' b, list.replicate m' c],
      split,
      {
        refl,
      },
      rw [
        list.replicate_succ_eq_append_singleton b,
        list.replicate_succ_eq_singleton_append c,
        list.append_assoc,
        list.append_assoc,
        ←list.append_assoc [R],
        ←list.append_assoc [b],
        ←list.append_assoc (list.replicate m' b)
      ],
      refl,
    },
    unfold CF_language,
    rw set.mem_set_of_eq,
    unfold CF_generates,
    unfold CF_generates_str,
    have obtain_sum :
      CF_derives gr_add
        [symbol.nonterminal gr_add.initial]
        ((list.replicate n a) ++ (list.replicate m b) ++ [R] ++ (list.replicate (n + m) c)),
    {
      have middle_step : CF_derives gr_add
        ((list.replicate n a) ++ [S] ++ (list.replicate n c))
        ((list.replicate n a) ++ [R] ++ (list.replicate n c)),
      {
        apply CF_deri_with_prefix_and_postfix,
        apply CF_deri_of_tran,
        use (S_, [R]),
        split_ile,
        use [[], []],
        split;
        refl,
      },
      apply CF_deri_of_deri_deri,
      {
        specialize epoch_a n,
        finish,
      },
      apply CF_deri_of_deri_deri,
      {
        finish,
      },
      change
        CF_derives gr_add
          (list.replicate n a ++ ([R] ++ list.replicate n c))
          (list.replicate n a ++ list.replicate m b ++ [R] ++ list.replicate (n + m) c),
      rw ←list.append_assoc,
      have cnm : list.replicate (n + m) c = list.replicate m c ++ list.replicate n c,
      {
        rw add_comm,
        apply list.replicate_add,
      },
      rw cnm,
      have rebra : (list.replicate n a ++ list.replicate m b ++ [R] ++ (list.replicate m c ++ list.replicate n c)) =
                   (list.replicate n a ++ (list.replicate m b ++ [R] ++ list.replicate m c) ++ list.replicate n c),
      {
        simp only [list.append_assoc],
      },
      rw rebra,
      apply CF_deri_with_prefix_and_postfix,
      exact epoch_b m,
    },
    apply CF_deri_of_deri_tran obtain_sum,
    use (R_, []),
    split_ile,
    use (list.replicate n a ++ list.replicate m b),
    use list.replicate (n + m) c,
    split,
    {
      refl,
    },
    unfold anbmcnm,
    rw list.map_append_append,
    rw list.append_nil,
    repeat {
      rw list.map_replicate,
    },
    refl,
  },
end
