import context_free.cfg
import tactic


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

  apply CF_deri_of_tran_deri,
  {
    use (S_, [a, S, c]),
    split,
    {
      in_list_explicit,
    },
    use [[], []],
    simp,
  },

  apply CF_deri_of_tran_deri,
  {
    use (S_, [a, S, c]),
    split,
    {
      in_list_explicit,
    },
    use [[a], [c]],
    rw S,
    simp,
  },

  apply CF_deri_of_tran_deri,
  {
    use (S_, [R]),
    split,
    {
      in_list_explicit,
    },
    use [[a, a], [c, c]],
    simp,
  },

  apply CF_deri_of_tran_deri,
  {
    use (R_, [b, R, c]),
    split,
    {
      in_list_explicit,
    },
    use [[a, a], [c, c]],
    rw R,
    simp,
  },

  apply CF_deri_of_tran,
  {
    use (R_, []),
    split,
    {
      in_list_explicit,
    },
    use [[a, a, b], [c, c, c]],
    repeat { try {split}, try {refl} },
  },
end


private def anbmcnm (n m : ℕ) : list (fin 3) :=
list.repeat a_ n ++ list.repeat b_ m ++ list.repeat c_ (n + m)

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
    intro ass,
    change CF_derives gramatika [S] (list.map symbol.terminal x) at ass,

    have possib : ∀ w : list (symbol (fin 3) gramatika.nt),
      CF_derives gramatika [S] w →
        (∃ i : ℕ, w = list.repeat a i ++ [S] ++ list.repeat c i) ∨
        (∃ i j : ℕ, w = list.repeat a i ++ list.repeat b j ++ [R] ++ list.repeat c (i + j)) ∨
        (∃ i j : ℕ, w = list.repeat a i ++ list.repeat b j ++ list.repeat c (i + j)),
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
        -- the case `list.repeat a i ++ [S] ++ list.repeat c i` matches 1st and 2nd rule
        cases rule_in,
        {
          left,
          cases case₁ with i the_case,
          rw list.append_assoc at the_case,
          use i + 1,
          have almost : z = list.repeat a i ++ [a, S, c] ++ list.repeat c i,
          {
            rw hyp_bef at the_case,
            rw hyp_aft,
            rw rule_in at *,
            have u_must : u = list.repeat a i,
            {
              dsimp at *,
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
                rw list.take_append_of_le_length (le_of_eq (list.length_repeat a i).symm) at indexS,
                rw list.take_repeat at indexS,
                rw min_self at indexS,
                rw ←list.length_repeat a i at hlt,
                have please : (list.repeat a i).nth_le u.length hlt = S,
                {
                  rw list.nth_le_nth hlt at indexS,
                  injection indexS,
                },
                rw list.nth_le_repeat a hlt at please,
                injection please,
              },
              cases hge.symm with hgt heq,
              {
                exfalso,
                rw the_case at indexS,
                have rightend : u.length < (list.repeat a i ++ [S] ++ list.repeat c i).length,
                {
                  have thelength := congr_arg list.length the_case,
                  rw list.append_assoc at thelength,
                  rw list.length_append at thelength,
                  rw list.append_assoc,
                  change u.length < (list.repeat a i ++ S :: list.repeat c i).length,
                  rw ←thelength,
                  rw list.length_append,
                  dsimp,
                  rw ←add_assoc,
                  apply lt_of_lt_of_le,
                  {
                    exact lt_add_one u.length,
                  },
                  exact le_self_add,
                },
                change (list.repeat a i ++ ([S] ++ list.repeat c i)).nth u.length = some S at indexS,
                rw ←list.append_assoc at indexS,
                rw list.nth_le_nth rightend at indexS,
                injection indexS with continue,
                have mala : (list.repeat a i ++ [S]).length ≤ u.length,
                {
                  rw list.length_append,
                  dsimp,
                  rw list.length_repeat a i,
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
            have v_must : v = list.repeat c i,
            {
              rw u_must at the_case,
              rw list.append_assoc at the_case,
              rw list.append_right_inj (list.repeat a i) at the_case,
              rw ←S at the_case,
              rw list.append_right_inj [S] at the_case,
              exact the_case,
            },
            rw u_must,
            rw v_must,
          },
          rw list.repeat_add,
          change z = list.repeat a i ++ [a] ++ [S] ++ list.repeat c (i + 1),
          rw add_comm,
          rw list.repeat_add,
          change z = list.repeat a i ++ [a] ++ [S] ++ ([c] ++ list.repeat c i),
          rw ←list.append_assoc,
          rw list.append_assoc (list.repeat a i) [a],
          rw list.append_assoc (list.repeat a i) ([a] ++ [S]),
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
          have u_must : u = list.repeat a i,
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
              change u ++ ([S] ++ v) = list.repeat a i ++ ([S] ++ list.repeat c i) at the_case,
              rw list.append_assoc at indexS,
              rw the_case at indexS,
              rw list.take_append_of_le_length (le_of_eq (list.length_repeat a i).symm) at indexS,
              rw list.take_repeat at indexS,
              rw min_self at indexS,
              rw ←list.length_repeat a i at hlt,
              have please : (list.repeat a i).nth_le u.length hlt = S,
              {
                rw list.nth_le_nth hlt at indexS,
                injection indexS,
              },
              rw list.nth_le_repeat a hlt at please,
              injection please,
            },
            cases hge.symm with hgt heq,
            {
              exfalso,
              rw list.append_assoc at the_case,
              rw hyp_bef at the_case,
              rw rule_in at *,
              change u ++ [S] ++ v = list.repeat a i ++ S :: list.repeat c i at the_case,
              rw the_case at indexS,
              have rightend : u.length < (list.repeat a i ++ [S] ++ list.repeat c i).length,
              {
                have thelength := congr_arg list.length the_case,
                rw list.append_assoc at thelength,
                rw list.length_append at thelength,
                rw list.append_assoc,
                change u.length < (list.repeat a i ++ S :: list.repeat c i).length,
                rw ←thelength,
                rw list.length_append,
                dsimp,
                rw ←add_assoc,
                apply lt_of_lt_of_le,
                {
                  exact lt_add_one u.length,
                },
                exact le_self_add,
              },
              change (list.repeat a i ++ ([S] ++ list.repeat c i)).nth u.length = some S at indexS,
              rw ←list.append_assoc at indexS,
              rw list.nth_le_nth rightend at indexS,
              injection indexS with continue,
              have mala : (list.repeat a i ++ [S]).length ≤ u.length,
              {
                rw list.length_append,
                dsimp,
                rw list.length_repeat a i,
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
            rw list.length_repeat a i,
          },
          have v_must : v = list.repeat c i,
          {
            rw list.append_assoc at the_case,
            rw hyp_bef at the_case,
            rw list.append_assoc at the_case,
            rw u_must at the_case,
            rw list.append_right_inj (list.repeat a i) at the_case,
            rw rule_in at the_case,
            change [S] ++ v = [S] ++ list.repeat c i at the_case,
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
            rw list.mem_repeat at contra,
            have triv : R ≠ a,
            {
              tauto,
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
            rw list.mem_repeat at contra,
            have triv : R ≠ c,
            {
              tauto,
            },
            exact triv contra.right,
          },
        },
        exfalso,
        exact (list.mem_nil_iff rule).1 rule_in,
      },
      cases caseᵣ with case₂ case₃,
      {
        -- the case `list.repeat a i ++ list.repeat b j ++ [R] ++ list.repeat c (i + j)` matches 3rd and 4th rule
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
            rw list.mem_repeat at contra,
            have triv : S ≠ a,
            {
              tauto,
            },
            exact triv contra.right,
          },
          cases contra,
          {
            rw list.mem_repeat at contra,
            have triv : S ≠ b,
            {
              tauto,
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
            rw list.mem_repeat at contra,
            have triv : S ≠ c,
            {
              tauto,
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
          have u_eq : u = list.repeat a i ++ list.repeat b j,
          {
            cases @trichotomous ℕ (<) _ u.length (i + j) with hlt rest,
            {
              exfalso,
              rw ←list.nth_take hlt at indexR,
              have h_len : u.length < (list.repeat a i ++ list.repeat b j).length,
              {
                rw list.length_append,
                rw list.length_repeat,
                rw list.length_repeat,
                exact hlt,
              },
              have propos : (list.repeat a i ++ list.repeat b j).nth_le u.length h_len = R,
              {
                change list.repeat a i ++ (list.repeat b j ++ R :: list.repeat c (i + j)) = u ++ ([R] ++ v) at hyp_bef,
                rw ←list.append_assoc u [R] v at hyp_bef,
                rw ←hyp_bef at indexR,
                rw ←list.append_assoc at indexR,
                have take_beg : list.take (i + j) (list.repeat a i ++ list.repeat b j ++ R :: list.repeat c (i + j)) = (list.repeat a i ++ list.repeat b j),
                {
                  have len_ij : (list.repeat a i ++ list.repeat b j).length = i + j,
                  {
                    rw list.length_append,
                    rw list.length_repeat,
                    rw list.length_repeat,
                  },
                  rw list.take_append_of_le_length (le_of_eq len_ij.symm),
                  rw list.take_all_of_le,
                  exact le_of_eq len_ij,
                },
                rw take_beg at indexR,
                rw list.nth_le_nth h_len at indexR,
                injection indexR,
              },
              have yes_R : R ∈ (list.repeat a i ++ list.repeat b j),
              {
                let positive := list.nth_le_mem (list.repeat a i ++ list.repeat b j) u.length h_len,
                rw propos at positive,
                exact positive,
              },
              have not_R : R ∉ (list.repeat a i ++ list.repeat b j),
              {
                rw list.mem_append,
                push_neg,
                split,
                {
                  have nidRa : R ≠ a,
                  {
                    tauto,
                  },
                  by_contradiction,
                  rw list.mem_repeat at h,
                  exact nidRa h.right,
                },
                {
                  have nidRb : R ≠ b,
                  {
                    tauto,
                  },
                  by_contradiction,
                  rw list.mem_repeat at h,
                  exact nidRb h.right,
                },
              },
              exact not_R yes_R,
            },
            cases rest.symm with hgt heq,
            {
              exfalso,
              have yes_Rc : R ∈ list.repeat c (i + j),
              {
                change
                  list.repeat a i ++ (list.repeat b j ++ R :: list.repeat c (i + j)) = u ++ ([R] ++ v)
                  at hyp_bef,
                rw ←list.append_assoc u [R] v at hyp_bef,
                rw ←hyp_bef at indexR,
                rw ←list.append_assoc at indexR,
                change
                  (list.repeat a i ++ list.repeat b j ++ ([R] ++ list.repeat c (i + j))).nth u.length = some R
                  at indexR,
                rw ←list.append_assoc at indexR,
                rw list.nth_append_right at indexR,
                {
                  simp at indexR,
                  have trouble_len : (u.length - (i + (j + 1))) < (list.repeat c (i + j)).length,
                  {
                    rw list.length_repeat,
                    have lengths_sum : u.length ≤ i + j + i + j,
                    {
                      let lengs := congr_arg list.length hyp_bef,
                      repeat {
                        rw list.length_append at lengs,
                      },
                      rw list.length_repeat at lengs,
                      rw list.length_repeat at lengs,
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
                rw list.length_repeat,
                rw list.length_repeat,
                convert hgt,
              },
              have not_Rc : R ∉ list.repeat c (i + j),
              {
                by_contradiction,
                rw list.mem_repeat at h,
                have nidRc : R ≠ c,
                {
                  tauto,
                },
                exact nidRc h.right,
              },
              exact not_Rc yes_Rc,
            },
            rw ←list.append_assoc at hyp_bef,
            have lenlen : (list.repeat a i ++ list.repeat b j).length = u.length,
            {
              rw list.length_append,
              rw list.length_repeat,
              rw list.length_repeat,
              exact heq.symm,
            },
            symmetry,
            exact list.append_inj_left hyp_bef lenlen,
          },
          have v_eq : v = list.repeat c (i + j),
          {
            rw u_eq at hyp_bef,
            rw ←list.append_assoc at hyp_bef,
            rw list.append_right_inj (list.repeat a i ++ list.repeat b j) at hyp_bef,
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
          have bpp : list.repeat b (j + 1) = list.repeat b j ++ [b],
          {
            rw list.repeat_add b j 1,
            refl,
          },
          have cpp : list.repeat c (i + (j + 1)) = [c] ++ list.repeat c (i + j),
          {
            rw ←add_assoc,
            rw add_comm,
            rw list.repeat_add c 1 (i + j),
            refl,
          },
          rw bpp,
          rw cpp,
          rw list.append_assoc,
          apply congr_arg (λ lis, list.repeat a i ++ lis),
          rw list.append_assoc,
          apply congr_arg (λ lis, list.repeat b j ++ lis),
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
        -- the remaining case `list.repeat a i ++ list.repeat b j ++ list.repeat c (i + j)` does not match any rule
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
            tauto,
          },
          rw list.mem_repeat at contra,
          apply neq,
          exact contra.right,
        },
        cases contra,
        {
          have neq : symbol.nonterminal rule.fst ≠ b,
          {
            tauto,
          },
          rw list.mem_repeat at contra,
          apply neq,
          exact contra.right,
        },
        {
          have neq : symbol.nonterminal rule.fst ≠ c,
          {
            tauto,
          },
          rw list.mem_repeat at contra,
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
    rw ←list.map_repeat symbol.terminal a_ n at keyprop,
    rw ←list.map_repeat symbol.terminal b_ m at keyprop,
    rw ←list.map_repeat symbol.terminal c_ (n + m) at keyprop,
    rw ←list.map_append at keyprop,
    rw ←list.map_append at keyprop,

    ext1 k,
    have kprop := congr_fun (congr_arg list.nth keyprop) k,
    rw list.nth_map at kprop,
    rw list.nth_map at kprop,

    cases x.nth k,
    {
      cases (list.repeat a_ n ++ list.repeat b_ m ++ list.repeat c_ (n + m)).nth k,
      {
        refl,
      },
      {
        exfalso,
        injection kprop,
      },
    },
    {
      cases (list.repeat a_ n ++ list.repeat b_ m ++ list.repeat c_ (n + m)).nth k,
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
    -- prove `x ∈ CF_language gramatika ← x ∈ language_abc` here
    intro h,
    cases h with n hy,
    cases hy with m hyp,
    rw hyp,

    have epoch_a : ∀ i : ℕ, CF_derives gramatika [S] ((list.repeat a i) ++ [S] ++ (list.repeat c i)),
    {
      intro i,
      induction i with n' ih,
      {
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran ih,

      use (S_, [a, S, c]),
      split,
      {
        in_list_explicit,
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
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran jh,

      use (R_, [b, R, c]),
      split,
      {
        in_list_explicit,
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
        apply CF_deri_with_prefix_and_postfix,
        apply CF_deri_of_tran,
        use (S_, [R]),
        split,
        {
          in_list_explicit,
        },
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
      change CF_derives gramatika (list.repeat a n ++ ([R] ++ list.repeat c n)) (list.repeat a n ++ list.repeat b m ++ [R] ++ list.repeat c (n + m)),
      rw ←list.append_assoc,
      have cnm : list.repeat c (n + m) = list.repeat c m ++ list.repeat c n,
      {
        rw add_comm,
        apply list.repeat_add,
      },
      rw cnm,
      have rebra : (list.repeat a n ++ list.repeat b m ++ [R] ++ (list.repeat c m ++ list.repeat c n)) =
                   (list.repeat a n ++ (list.repeat b m ++ [R] ++ list.repeat c m) ++ list.repeat c n),
      {
        simp only [list.append_assoc],
      },
      rw rebra,
      apply CF_deri_with_prefix_and_postfix,
      exact epoch_b m,
    },
    use (R_, []),
    split,
    {
      in_list_explicit,
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
