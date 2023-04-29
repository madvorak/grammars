import classes.unrestricted.lifting
import classes.unrestricted.closure_properties.concatenation


-- new nonterminal type
private def nn (N : Type) : Type :=
N ⊕ fin 3

-- new symbol type
private def ns (T N : Type) : Type :=
symbol T (nn N)

variables {T : Type}


section specific_symbols

private def Z {N : Type} : ns T N := symbol.nonterminal (sum.inr 0)
private def H {N : Type} : ns T N := symbol.nonterminal (sum.inr 1) -- denoted by `#` in the pdf
private def R {N : Type} : ns T N := symbol.nonterminal (sum.inr 2)

private def S {g : grammar T} : ns T g.nt := symbol.nonterminal (sum.inl g.initial)

private lemma Z_neq_H {N : Type} :  Z ≠ @H T N  :=
begin
  intro ass,
  have imposs := sum.inr.inj (symbol.nonterminal.inj ass),
  exact fin.zero_ne_one imposs,
end

private lemma Z_neq_R {N : Type} :  Z ≠ @R T N  :=
begin
  intro ass,
  have imposs := sum.inr.inj (symbol.nonterminal.inj ass),
  have zero_ne_two : (0 : fin 3) ≠ (2 : fin 3), dec_trivial,
  exact zero_ne_two imposs,
end

private lemma H_neq_R {N : Type} :  H ≠ @R T N  :=
begin
  intro ass,
  have imposs := sum.inr.inj (symbol.nonterminal.inj ass),
  have one_ne_two : (1 : fin 3) ≠ (2 : fin 3), dec_trivial,
  exact one_ne_two imposs,
end

end specific_symbols


section construction

private def wrap_sym {N : Type} : symbol T N → ns T N
| (symbol.terminal t)    := symbol.terminal t
| (symbol.nonterminal n) := symbol.nonterminal (sum.inl n)

private def wrap_gr {N : Type} (r : grule T N) : grule T (nn N) :=
grule.mk
  (list.map wrap_sym r.input_L)
  (sum.inl r.input_N)
  (list.map wrap_sym r.input_R)
  (list.map wrap_sym r.output_string)

private def rules_that_scan_terminals (g : grammar T) : list (grule T (nn g.nt)) :=
list.map (λ t, grule.mk
    [] (sum.inr 2) [symbol.terminal t] [symbol.terminal t, R]
  ) (all_used_terminals g)

-- based on `/informal/KleeneStar.pdf`
private def star_grammar (g : grammar T) : grammar T :=
grammar.mk (nn g.nt) (sum.inr 0) (
  grule.mk [] (sum.inr 0) [] [Z, S, H] ::
  grule.mk [] (sum.inr 0) [] [R, H] ::
  grule.mk [] (sum.inr 2) [H] [R] ::
  grule.mk [] (sum.inr 2) [H] [] ::
  list.map wrap_gr g.rules ++
  rules_that_scan_terminals g
)

end construction


section easy_direction

private lemma short_induction {g : grammar T} {w : list (list T)}
    (ass : ∀ wᵢ ∈ w.reverse, grammar_generates g wᵢ) :
  grammar_derives (star_grammar g) [Z] (Z ::
      list.join (list.map (++ [H]) (list.map (list.map symbol.terminal) w.reverse))
    )  ∧
  ∀ p ∈ w, ∀ t ∈ p, symbol.terminal t ∈ list.join (list.map grule.output_string g.rules)  :=
begin
  induction w with v x ih,
  {
    split,
    {
      apply grammar_deri_self,
    },
    {
      intros p pin,
      exfalso,
      exact list.not_mem_nil p pin,
    },
  },
  have vx_reverse : (v :: x).reverse = x.reverse ++ [v],
  {
    apply list.reverse_cons,
  },
  rw vx_reverse at *,
  specialize ih (by {
    intros wᵢ in_reversed,
    apply ass,
    apply list.mem_append_left,
    exact in_reversed,
  }),
  specialize ass v (by {
    apply list.mem_append_right,
    apply list.mem_singleton_self,
  }),
  unfold grammar_generates at ass,
  split,
  {
    apply grammar_deri_of_tran_deri,
    {
      use (star_grammar g).rules.nth_le 0 (by dec_trivial),
      split,
      {
        apply list.nth_le_mem,
      },
      use [[], []],
      split;
      refl,
    },
    rw [list.nil_append, list.append_nil, list.map_append, list.map_append],
    change grammar_derives (star_grammar g) [Z, S, H] _,
    have ih_plus := grammar_deri_with_postfix ([S, H] : list (symbol T (star_grammar g).nt)) ih.left,
    apply grammar_deri_of_deri_deri ih_plus,
    have ass_lifted : grammar_derives (star_grammar g) [S] (list.map symbol.terminal v),
    {
      clear_except ass,
      have wrap_eq_lift : @wrap_sym T g.nt = lift_symbol sum.inl,
      {
        ext,
        cases x;
        refl,
      },
      let lifted_g : lifted_grammar T :=
        lifted_grammar.mk g (star_grammar g) sum.inl sum.get_left (by {
          intros x y hyp,
          exact sum.inl.inj hyp,
        }) (by {
          intros x y hyp,
          cases x,
          {
            cases y,
            {
              simp only [sum.get_left] at hyp,
              left,
              congr,
              exact hyp,
            },
            {
              simp only [sum.get_left] at hyp,
              exfalso,
              exact hyp,
            },
          },
          {
            cases y,
            {
              simp only [sum.get_left] at hyp,
              exfalso,
              exact hyp,
            },
            {
              right,
              refl,
            },
          },
        }) (by {
          intro x,
          refl,
        }) (by {
          intros r rin,
          apply list.mem_cons_of_mem,
          apply list.mem_cons_of_mem,
          apply list.mem_cons_of_mem,
          apply list.mem_cons_of_mem,
          apply list.mem_append_left,
          rw list.mem_map,
          use r,
          split,
          {
            exact rin,
          },
          unfold wrap_gr,
          unfold lift_rule,
          unfold lift_string,
          rw wrap_eq_lift,
        }) (by {
          rintros r ⟨rin, n, nrn⟩,
          iterate 4 {
            cases rin,
            {
              exfalso,
              rw rin at nrn,
              exact sum.no_confusion nrn,
            },
          },
          change r ∈ list.map wrap_gr g.rules ++ rules_that_scan_terminals g at rin,
          rw list.mem_append at rin,
          cases rin,
          {
            clear_except rin wrap_eq_lift,
            rw list.mem_map at rin,
            rcases rin with ⟨r₀, rin₀, r_of_r₀⟩,
            use r₀,
            split,
            {
              exact rin₀,
            },
            convert r_of_r₀,
            unfold lift_rule,
            unfold wrap_gr,
            unfold lift_string,
            rw wrap_eq_lift,
          },
          {
            exfalso,
            unfold rules_that_scan_terminals at rin,
            rw list.mem_map at rin,
            rcases rin with ⟨t, tin, r_of_tg⟩,
            rw ←r_of_tg at nrn,
            exact sum.no_confusion nrn,
          },
        }),
      convert_to
        grammar_derives lifted_g.g
          [symbol.nonterminal (sum.inl g.initial)]
          (lift_string lifted_g.lift_nt (list.map symbol.terminal v)),
      {
        unfold lift_string,
        rw list.map_map,
        congr,
      },
      exact lift_deri lifted_g ass,
    },
    have ass_postf := grammar_deri_with_postfix ([H] : list (symbol T (star_grammar g).nt)) ass_lifted,
    rw list.join_append,
    rw ←list.cons_append,
    apply grammar_deri_with_prefix,
    rw list.map_map,
    rw list.map_singleton,
    rw list.join_singleton,
    change grammar_derives (star_grammar g) [S, H] (list.map symbol.terminal v ++ [H]),
    convert ass_postf,
  },
  {
    intros p pin t tin,
    cases pin,
    {
      rw pin at tin,
      clear pin,
      have stin : symbol.terminal t ∈ list.map symbol.terminal v,
      {
        rw list.mem_map,
        use t,
        split,
        {
          exact tin,
        },
        {
          refl,
        },
      },
      cases grammar_generates_only_legit_terminals ass stin with rule_exists imposs,
      {
        rcases rule_exists with ⟨r, rin, stirn⟩,
        rw list.mem_join,
        use r.output_string,
        split,
        {
          rw list.mem_map,
          use r,
          split,
          {
            exact rin,
          },
          {
            refl,
          },
        },
        {
          exact stirn,
        },
      },
      {
        exfalso,
        exact symbol.no_confusion imposs,
      }
    },
    {
      exact ih.right p pin t tin,
    }
  },
end

private lemma terminal_scan_ind {g : grammar T} {w : list (list T)} (n : ℕ) (n_lt_wl : n ≤ w.length)
    (terminals : ∀ v ∈ w, ∀ t ∈ v, symbol.terminal t ∈ list.join (list.map grule.output_string g.rules)) :
  grammar_derives (star_grammar g)
    ((list.map (λ u, list.map symbol.terminal u) (list.take (w.length - n) w)).join ++ [R] ++
      (list.map (λ v, [H] ++ list.map symbol.terminal v) (list.drop (w.length - n) w)).join ++ [H])
    (list.map symbol.terminal w.join ++ [R, H])  :=
begin
  induction n with k ih,
  {
    rw nat.sub_zero,
    rw list.drop_length,
    rw list.map_nil,
    rw list.join,
    rw list.append_nil,
    rw list.take_length,
    rw list.map_join,
    rw list.append_assoc,
    apply grammar_deri_self,
  },
  specialize ih (nat.le_of_succ_le n_lt_wl),
  apply grammar_deri_of_deri_deri _ ih,
  clear ih,

  have wlk_succ : w.length - k = (w.length - k.succ).succ,
  {
    omega,
  },
  have lt_wl : w.length - k.succ < w.length,
  {
    omega,
  },
  have split_ldw :
    list.drop (w.length - k.succ) w =
    (w.nth (w.length - k.succ)).to_list ++ list.drop (w.length - k) w,
  {
    rw wlk_succ,
    generalize substit : w.length - k.succ = q,
    rw substit at lt_wl,
    rw ←list.take_append_drop q w,
    rw list.nth_append_right,
    swap, {
      apply list.length_take_le,
    },
    have eq_q : (list.take q w).length = q,
    {
      rw list.length_take,
      exact min_eq_left_of_lt lt_wl,
    },
    rw eq_q,
    rw nat.sub_self,
    have drop_q_succ :
      list.drop q.succ (list.take q w ++ list.drop q w) = list.drop 1 (list.drop q w),
    {
      rw list.drop_drop,
      rw list.take_append_drop,
      rw add_comm,
    },
    rw [drop_q_succ, list.drop_left' eq_q, list.drop_drop],
    rw ←list.take_append_drop (1 + q) w,
    have q_lt : q < (list.take (1 + q) w).length,
    {
      rw list.length_take,
      exact lt_min (lt_one_add q) lt_wl,
    },
    rw list.drop_append_of_le_length (le_of_lt q_lt),
    apply congr_arg2,
    {
      rw list.nth_append,
      swap, {
        rw list.length_drop,
        exact nat.sub_pos_of_lt q_lt,
      },
      rw list.nth_drop,
      rw add_zero,
      rw list.nth_take (lt_one_add q),
      rw add_comm,
      rw list_drop_take_succ lt_wl,
      rw list.nth_le_nth lt_wl,
      refl,
    },
    {
      rw list.take_append_drop,
    },
  },
  apply grammar_deri_with_postfix,
  rw [split_ldw, list.map_append, list.join_append, ←list.append_assoc],
  apply grammar_deri_with_postfix,
  rw [wlk_succ, list.take_succ, list.map_append, list.join_append, list.append_assoc, list.append_assoc],
  apply grammar_deri_with_prefix,
  clear_except terminals lt_wl,
  specialize terminals (w.nth_le (w.length - k.succ) lt_wl) (list.nth_le_mem w (w.length - k.succ) lt_wl),
  rw list.nth_le_nth lt_wl,
  unfold option.to_list,
  rw [list.map_singleton, list.join_singleton, ←list.map_join, list.join_singleton],
  apply grammar_deri_of_tran_deri,
  {
    use (star_grammar g).rules.nth_le 2 (by dec_trivial),
    split_ile,
    use [[], list.map symbol.terminal (w.nth_le (w.length - k.succ) lt_wl)],
    split;
    refl,
  },
  rw list.nil_append,

  have scan_segment : ∀ m : ℕ, m ≤ (w.nth_le (w.length - k.succ) lt_wl).length →
    grammar_derives (star_grammar g)
      ([R] ++ list.map symbol.terminal (w.nth_le (w.length - k.succ) lt_wl))
      (list.map symbol.terminal (list.take m (w.nth_le (w.length - k.succ) lt_wl)) ++
        ([R] ++ list.map symbol.terminal (list.drop m (w.nth_le (w.length - k.succ) lt_wl)))),
  {
    intros m small,
    induction m with n ih,
    {
      rw ←list.append_assoc,
      convert grammar_deri_self,
    },
    apply grammar_deri_of_deri_tran (ih (nat.le_of_succ_le small)),
    rw nat.succ_le_iff at small,
    use ⟨[], (sum.inr 2), [symbol.terminal (list.nth_le (w.nth_le (w.length - k.succ) lt_wl) n small)],
      [symbol.terminal (list.nth_le (w.nth_le (w.length - k.succ) lt_wl) n small), R]⟩,
    split,
    {
      iterate 4 {
        apply list.mem_cons_of_mem,
      },
      apply list.mem_append_right,
      unfold rules_that_scan_terminals,
      rw list.mem_map,
      use list.nth_le (w.nth_le (w.length - k.succ) lt_wl) n small,
      split,
      {
        unfold all_used_terminals,
        rw list.mem_filter_map,
        use (w.nth_le (w.length - k.succ) lt_wl).nth_le n small,
        split,
        {
          apply terminals,
          apply list.nth_le_mem,
        },
        {
          refl,
        },
      },
      {
        refl,
      },
    },
    use list.map symbol.terminal (list.take n (w.nth_le (w.length - k.succ) lt_wl)),
    use list.map symbol.terminal (list.drop n.succ (w.nth_le (w.length - k.succ) lt_wl)),
    dsimp only,
    split,
    {
      trim,
      rw list.nil_append,
      rw list.append_assoc,
      apply congr_arg2,
      {
        refl,
      },
      rw ←list.take_append_drop 1 (list.map symbol.terminal (list.drop n (w.nth_le (w.length - k.succ) lt_wl))),
      apply congr_arg2,
      {
        rw ←list.map_take,
        rw list_take_one_drop,
        rw list.map_singleton,
      },
      {
        rw ←list.map_drop,
        rw list.drop_drop,
        rw add_comm,
      },
    },
    {
      rw list.take_succ,
      rw list.map_append,
      trim,
      rw list.nth_le_nth small,
      refl,
    },
  },
  convert scan_segment (w.nth_le (w.length - k.succ) lt_wl).length (by refl),
  {
    rw list.take_length,
  },
  {
    rw list.drop_length,
    rw list.map_nil,
    refl,
  },
end

private lemma terminal_scan_aux {g : grammar T} {w : list (list T)}
    (terminals : ∀ v ∈ w, ∀ t ∈ v, symbol.terminal t ∈ list.join (list.map grule.output_string g.rules)) :
  grammar_derives (star_grammar g)
    ([R] ++ (list.map (λ v, [H] ++ v) (list.map (list.map symbol.terminal) w)).join ++ [H])
    (list.map symbol.terminal w.join ++ [R, H])  :=
begin
  rw list.map_map,
  convert terminal_scan_ind w.length (by refl) terminals,
  {
    rw nat.sub_self,
    rw list.take_zero,
    refl,
  },
  {
    rw nat.sub_self,
    refl,
  },
end

end easy_direction


section hard_direction

lemma zero_of_not_ge_one {n : ℕ} (not_pos : ¬ (n ≥ 1)) :  n = 0  :=
begin
  push_neg at not_pos,
  rwa nat.lt_one_iff at not_pos,
end

lemma length_ge_one_of_not_nil {α : Type*} {l : list α} (lnn : l ≠ []) :  l.length ≥ 1  :=
begin
  by_contradiction contra,
  have llz := zero_of_not_ge_one contra,
  rw list.length_eq_zero at llz,
  exact lnn llz,
end

private lemma nat_eq_tech {a b c : ℕ} (b_lt_c : b < c) (ass : c = a.succ + c - b.succ) :
  a = b  :=
begin
  omega,
end

private lemma wrap_never_outputs_nt_inr {N : Type} {a : symbol T N} (i : fin 3) :
  wrap_sym a ≠ symbol.nonterminal (sum.inr i)  :=
begin
  cases a;
  unfold wrap_sym,
  {
    apply symbol.no_confusion,
  },
  intro contr,
  have inl_eq_inr := symbol.nonterminal.inj contr,
  exact sum.no_confusion inl_eq_inr,
end

private lemma wrap_never_outputs_Z {N : Type} {a : symbol T N} :
  wrap_sym a ≠ Z  :=
begin
  exact wrap_never_outputs_nt_inr 0,
end

private lemma wrap_never_outputs_H {N : Type} {a : symbol T N} :
  wrap_sym a ≠ H  :=
begin
  exact wrap_never_outputs_nt_inr 1,
end

private lemma wrap_never_outputs_R {N : Type} {a : symbol T N} :
  wrap_sym a ≠ R  :=
begin
  exact wrap_never_outputs_nt_inr 2,
end

private lemma map_wrap_never_contains_nt_inr {N : Type} {l : list (symbol T N)} (i : fin 3) :
  symbol.nonterminal (sum.inr i) ∉ list.map wrap_sym l  :=
begin
  intro contra,
  rw list.mem_map at contra,
  rcases contra with ⟨s, -, imposs⟩,
  exact wrap_never_outputs_nt_inr i imposs,
end

private lemma map_wrap_never_contains_Z {N : Type} {l : list (symbol T N)} :
  Z ∉ list.map wrap_sym l  :=
begin
  exact map_wrap_never_contains_nt_inr 0,
end

private lemma map_wrap_never_contains_H {N : Type} {l : list (symbol T N)} :
  H ∉ list.map wrap_sym l  :=
begin
  exact map_wrap_never_contains_nt_inr 1,
end

private lemma map_wrap_never_contains_R {N : Type} {l : list (symbol T N)} :
  R ∉ list.map wrap_sym l  :=
begin
  exact map_wrap_never_contains_nt_inr 2,
end

private lemma wrap_sym_inj {N : Type} {a b : symbol T N} (wrap_eq : wrap_sym a = wrap_sym b) :
  a = b  :=
begin
  cases a,
  {
    cases b,
    {
      congr,
      exact symbol.terminal.inj wrap_eq,
    },
    {
      exfalso,
      exact symbol.no_confusion wrap_eq,
    },
  },
  {
    cases b,
    {
      exfalso,
      exact symbol.no_confusion wrap_eq,
    },
    {
      congr,
      unfold wrap_sym at wrap_eq,
      exact sum.inl.inj (symbol.nonterminal.inj wrap_eq),
    },
  },
end

private lemma wrap_str_inj {N : Type} {x y : list (symbol T N)}
    (wrap_eqs : list.map wrap_sym x = list.map wrap_sym y) :
  x = y  :=
begin
  ext1,
  have eqnth := congr_arg (λ l, list.nth l n) wrap_eqs,
  dsimp only at eqnth,
  rw list.nth_map at eqnth,
  rw list.nth_map at eqnth,

  cases x.nth n with xₙ,
  {
    cases y.nth n with yₙ,
    {
      refl,
    },
    {
      exfalso,
      exact option.no_confusion eqnth,
    },
  },
  {
    cases y.nth n with yₙ,
    {
      exfalso,
      exact option.no_confusion eqnth,
    },
    {
      congr,
      apply wrap_sym_inj,
      rw option.map_some' at eqnth,
      rw option.map_some' at eqnth,
      exact option.some.inj eqnth,
    },
  },
end

private lemma H_not_in_rule_input {g : grammar T} {r : grule T g.nt} :
  H ∉ list.map wrap_sym r.input_L ++ [symbol.nonterminal (sum.inl r.input_N)] ++
      list.map wrap_sym r.input_R :=
begin
  intro contra,
  rw list.mem_append at contra,
  cases contra,
  swap, {
    exact map_wrap_never_contains_H contra,
  },
  rw list.mem_append at contra,
  cases contra,
  {
    exact map_wrap_never_contains_H contra,
  },
  {
    rw list.mem_singleton at contra,
    have imposs := symbol.nonterminal.inj contra,
    exact sum.no_confusion imposs,
  },
end

private lemma snsri_not_in_join_mpHmmw {g : grammar T} {x : list (list (symbol T g.nt))} {i : fin 3}
    (snsri_neq_H : symbol.nonterminal (sum.inr i) ≠ @H T g.nt) :
  symbol.nonterminal (sum.inr i) ∉ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))  :=
begin
  intro contra,
  rw list.mem_join at contra,
  rw list.map_map at contra,
  rcases contra with ⟨l, l_in, in_l⟩,
  rw list.mem_map at l_in,
  rcases l_in with ⟨y, -, eq_l⟩,
  rw ←eq_l at in_l,
  rw function.comp_app at in_l,
  rw list.mem_append at in_l,
  cases in_l,
  {
    exact map_wrap_never_contains_nt_inr i in_l,
  },
  {
    rw list.mem_singleton at in_l,
    exact snsri_neq_H in_l,
  },
end

private lemma Z_not_in_join_mpHmmw {g : grammar T} {x : list (list (symbol T g.nt))} :
  Z ∉ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))  :=
begin
  exact snsri_not_in_join_mpHmmw Z_neq_H,
end

private lemma R_not_in_join_mpHmmw {g : grammar T} {x : list (list (symbol T g.nt))} :
  R ∉ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))  :=
begin
  exact snsri_not_in_join_mpHmmw H_neq_R.symm,
end

private lemma zero_Rs_in_the_long_part {g : grammar T} {x : list (list (symbol T g.nt))} [decidable_eq (ns T g.nt)] :
  list.count_in (list.map (++ [H]) (list.map (list.map wrap_sym) x)).join R = 0  :=
begin
  exact list.count_in_zero_of_notin R_not_in_join_mpHmmw,
end

private lemma cases_1_and_2_and_3a_match_aux {g : grammar T} {r₀ : grule T g.nt}
    {x : list (list (symbol T g.nt))} {u v : list (ns T g.nt)} (xnn : x ≠ [])
    (hyp : (list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))) =
      u ++ list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        list.map wrap_sym r₀.input_R ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : list (symbol T g.nt),
    u = list.join (list.map (++ [H]) (list.take m (list.map (list.map wrap_sym) x))) ++ list.map wrap_sym u₁
    ∧  list.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)  ∧
    v = list.map wrap_sym v₁ ++ [H] ++
        list.join (list.map (++ [H]) (list.drop m.succ (list.map (list.map wrap_sym) x)))  :=
begin
  have hypp :
    (list.map (++ [H]) (list.map (list.map wrap_sym) x)).join =
    u ++ (
      list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ list.map wrap_sym r₀.input_R
    ) ++ v,
  {
    simpa [list.append_assoc] using hyp,
  },
  have mid_brack : ∀ u', ∀ v',
    u' ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v' =
    u' ++ (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R) ++ v',
  {
    intros,
    simp only [list.append_assoc],
  },
  simp_rw mid_brack,
  clear hyp mid_brack,

  classical,
  have count_Hs := congr_arg (λ l, list.count_in l H) hypp,
  dsimp only at count_Hs,
  rw list.count_in_append at count_Hs,
  rw list.count_in_append at count_Hs,
  rw list.count_in_zero_of_notin H_not_in_rule_input at count_Hs,
  rw add_zero at count_Hs,
  rw [list.count_in_join, list.map_map, list.map_map] at count_Hs,

  have lens := congr_arg list.length hypp,
  rw list.length_append_append at lens,
  rw list.length_append_append at lens,
  rw list.length_singleton at lens,

  have ul_lt : u.length < list.length (list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))),
  {
    clear_except lens,
    linarith,
  },
  rcases list.take_join_of_lt ul_lt with ⟨m, k, mlt, klt, init_ul⟩,

  have vnn : v ≠ [],
  {
    by_contradiction v_nil,
    rw [v_nil, list.append_nil] at hypp,
    clear_except hypp xnn,
    have hlast := congr_arg (λ l : list (ns T g.nt), l.reverse.nth 0) hypp,
    dsimp only at hlast,
    rw [list.reverse_join, list.reverse_append, list.reverse_append_append, list.reverse_singleton] at hlast,
    have hhh : some H = ((list.map wrap_sym r₀.input_R).reverse ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ (list.map wrap_sym r₀.input_L).reverse ++ u.reverse).nth 0,
    {
      convert hlast,
      rw list.map_map,
      change some H = (list.map (λ l, list.reverse (l ++ [H])) (list.map (list.map wrap_sym) x)).reverse.join.nth 0,
      simp_rw list.reverse_append,
      rw list.map_map,
      change some H = (list.map (λ l, [H].reverse ++ (list.map wrap_sym l).reverse) x).reverse.join.nth 0,
      rw ←list.map_reverse,
      have xrnn : x.reverse ≠ [],
      {
        intro xr_nil,
        rw list.reverse_eq_iff at xr_nil,
        exact xnn xr_nil,
      },
      cases x.reverse with d l,
      {
        exfalso,
        exact xrnn rfl,
      },
      rw [list.map_cons, list.join, list.append_assoc],
      rw list.nth_append,
      swap, {
        rw list.length_reverse,
        rw list.length_singleton,
        exact one_pos,
      },
      rw list.reverse_singleton,
      refl,
    },
    rw ←list.map_reverse at hhh,
    cases r₀.input_R.reverse,
    {
      rw [list.map_nil, list.nil_append] at hhh,
      simp only [list.nth, list.cons_append] at hhh,
      exact sum.no_confusion (symbol.nonterminal.inj hhh),
    },
    {
      simp only [list.nth, list.map_cons, list.cons_append] at hhh,
      exact wrap_never_outputs_H hhh.symm,
    },
  },
  have urrrl_lt :
    list.length (u ++ (
      list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ list.map wrap_sym r₀.input_R
    )) <
    list.length (list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))),
  {
    have vl_pos : v.length > 0,
    {
      exact list.length_pos_of_ne_nil vnn,
    },
    clear_except lens vl_pos,
    rw list.length_append,
    rw list.length_append_append,
    rw list.length_singleton,
    linarith,
  },
  rcases list.drop_join_of_lt urrrl_lt with ⟨m', k', mlt', klt', last_vl⟩,

  have mxl : m < x.length,
  {
    rw list.length_map at mlt,
    rw list.length_map at mlt,
    exact mlt,
  },
  have mxl' : m' < x.length,
  {
    rw list.length_map at mlt',
    rw list.length_map at mlt',
    exact mlt',
  },
  have mxlmm : m < (list.map (list.map wrap_sym) x).length,
  {
    rwa list.length_map,
  },
  have mxlmm' : m' < (list.map (list.map wrap_sym) x).length,
  {
    rwa list.length_map,
  },
  use [m, list.take k (x.nth_le m mxl), list.drop k' (x.nth_le m' mxl')],

  have hyp_u := congr_arg (list.take u.length) hypp,
  rw list.append_assoc at hyp_u,
  rw list.take_left at hyp_u,
  rw init_ul at hyp_u,
  rw list.nth_le_map at hyp_u,
  swap, {
    exact mxlmm,
  },
  rw list.take_append_of_le_length at hyp_u,
  swap, {
    rw list.nth_le_map at klt,
    swap, {
      exact mxlmm,
    },
    rw list.length_append at klt,
    rw list.length_singleton at klt,
    rw list.nth_le_map at klt ⊢,
    iterate 2 {
      swap, {
        exact mxl,
      },
    },
    rw list.length_map at klt ⊢,
    rw nat.lt_succ_iff at klt,
    exact klt,
  },
  rw ←hyp_u at count_Hs,

  have hyp_v :=
    congr_arg (list.drop (list.length (u ++ (
        list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ list.map wrap_sym r₀.input_R
      )))) hypp,
  rw list.drop_left at hyp_v,
  rw last_vl at hyp_v,
  rw list.nth_le_map at hyp_v,
  swap, {
    exact mxlmm',
  },
  rw list.drop_append_of_le_length at hyp_v,
  swap, {
    rw list.nth_le_map at klt',
    swap, {
      exact mxlmm',
    },
    rw list.length_append at klt',
    rw list.length_singleton at klt',
    rw list.nth_le_map at klt' ⊢,
    iterate 2 {
      swap, {
        exact mxl',
      },
    },
    rw list.length_map at klt' ⊢,
    rw nat.lt_succ_iff at klt',
    exact klt',
  },
  rw ←hyp_v at count_Hs,

  have mm : m = m',
  {
    clear_except count_Hs mxl mxl' klt klt',
    rw [
      list.count_in_append, list.count_in_append, list.map_map,
      list.count_in_join, ←list.map_take, list.map_map,
      list.count_in_join, ←list.map_drop, list.map_map
    ] at count_Hs,
    change
      (list.map (λ w, list.count_in (list.map wrap_sym w ++ [H]) H) x).sum =
      (list.map (λ w, list.count_in (list.map wrap_sym w ++ [H]) H) (list.take m x)).sum + _ +
        (_ + (list.map (λ w, list.count_in (list.map wrap_sym w ++ [H]) H) (list.drop m'.succ x)).sum)
      at count_Hs,
    simp_rw list.count_in_append at count_Hs,

    have inside_wrap : ∀ y : list (symbol T g.nt), (list.map wrap_sym y).count_in H = 0,
    {
      intro,
      rw list.count_in_zero_of_notin,
      apply map_wrap_never_contains_H,
    },
    have inside_one : ∀ z : list (symbol T g.nt),
      (list.map wrap_sym z).count_in (@H T g.nt) + [@H T g.nt].count_in (@H T g.nt) = 1,
    {
      intro,
      rw list.count_in_singleton_eq H,
      rw inside_wrap,
    },
    simp_rw inside_one at count_Hs,
    repeat {
      rw [list.map_const, list.sum_const_nat, one_mul] at count_Hs,
    },
    rw [list.length_take, list.length_drop, list.nth_le_map', list.nth_le_map'] at count_Hs,
    rw min_eq_left (le_of_lt mxl) at count_Hs,
    have inside_take : (list.take k (list.map wrap_sym (x.nth_le m mxl))).count_in H = 0,
    {
      rw ←list.map_take,
      rw inside_wrap,
    },
    have inside_drop : (list.drop k' (list.map wrap_sym (x.nth_le m' mxl'))).count_in H + [H].count_in H = 1,
    {
      rw ←list.map_drop,
      rw inside_wrap,
      rw list.count_in_singleton_eq (@H T g.nt),
    },
    rw [inside_take, inside_drop] at count_Hs,
    rw [add_zero, ←add_assoc, ←nat.add_sub_assoc] at count_Hs,
    swap, {
      rwa nat.succ_le_iff,
    },
    exact nat_eq_tech mxl' count_Hs,
  },
  rw ←mm at *,

  split,
  {
    symmetry,
    convert hyp_u,
    {
      rw list.map_take,
    },
    {
      rw list.map_take,
      rw list.nth_le_map,
    },
  },
  split,
  swap, {
    symmetry,
    convert hyp_v,
    {
      rw list.map_drop,
      rw list.nth_le_map,
    },
    {
      rw list.map_drop,
      rw mm,
    },
  },
  rw [←hyp_u, ←hyp_v] at hypp,

  have mltx : m < x.length,
  {
    rw list.length_map at mlt,
    rw list.length_map at mlt,
    exact mlt,
  },
  have xxx : x = x.take m ++ [x.nth_le m mltx] ++ x.drop m.succ,
  {
    rw list.append_assoc,
    rw list.singleton_append,
    rw list.cons_nth_le_drop_succ,
    rw list.take_append_drop,
  },
  have hyppp :
    (list.map (++ [H]) (list.map (list.map wrap_sym) (x.take m ++ [x.nth_le m mltx] ++ x.drop m.succ))).join =
    (list.take m (list.map (++ [H]) (list.map (list.map wrap_sym) x))).join ++
      list.take k ((list.map (list.map wrap_sym) x).nth_le m mxlmm) ++
      (list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ list.map wrap_sym r₀.input_R) ++
      (list.drop k' ((list.map (list.map wrap_sym) x).nth_le m mxlmm) ++ [H] ++
      (list.drop m.succ (list.map (++ [H]) (list.map (list.map wrap_sym) x))).join),
  {
    convert hypp,
    exact xxx.symm,
  },
  clear_except hyppp mm,
  rw [
    list.map_append_append, list.map_append_append,
    list.join_append_append,
    list.append_assoc, list.append_assoc, list.append_assoc, list.append_assoc, list.append_assoc, list.append_assoc,
    list.map_take, list.map_take,
    list.append_right_inj,
    ←list.append_assoc, ←list.append_assoc, ←list.append_assoc, ←list.append_assoc, ←list.append_assoc,
    list.map_drop, list.map_drop,
    list.append_left_inj,
    list.map_singleton, list.map_singleton, list.join_singleton,
    list.append_left_inj
  ] at hyppp,
  rw list.nth_le_nth mltx,
  apply congr_arg,
  apply wrap_str_inj,
  rw hyppp,
  rw list.map_append_append,
  rw list.map_take,
  rw list.nth_le_map,
  swap, {
    exact mltx,
  },
  rw list.map_drop,
  rw list.map_append_append,
  rw list.map_singleton,
  rw ←list.append_assoc,
  rw ←list.append_assoc,
  apply congr_arg2,
  {
    refl,
  },
  congr,
  exact mm,
end

private lemma case_1_match_rule {g : grammar T} {r₀ : grule T g.nt}
    {x : list (list (symbol T g.nt))} {u v : list (ns T g.nt)}
    (hyp : Z :: (list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))) =
      u ++ list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        list.map wrap_sym r₀.input_R ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : list (symbol T g.nt),
    u = Z :: list.join (list.map (++ [H]) (list.take m (list.map (list.map wrap_sym) x))) ++ list.map wrap_sym u₁
    ∧  list.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)  ∧
    v = list.map wrap_sym v₁ ++ [H] ++
        list.join (list.map (++ [H]) (list.drop m.succ (list.map (list.map wrap_sym) x)))  :=
begin
  by_cases is_x_nil : x = [],
  {
    exfalso,
    rw [is_x_nil, list.map_nil, list.map_nil, list.join] at hyp,
    have hyp_len := congr_arg list.length hyp,
    rw list.length_singleton at hyp_len,
    repeat {
      rw list.length_append at hyp_len,
    },
    rw list.length_singleton at hyp_len,
    have left_nil : u ++ list.map wrap_sym r₀.input_L = [],
    {
      rw ←list.length_eq_zero,
      rw list.length_append,
      omega,
    },
    have right_nil : list.map wrap_sym r₀.input_R ++ v = [],
    {
      rw ←list.length_eq_zero,
      rw list.length_append,
      omega,
    },
    rw [left_nil, list.nil_append, list.append_assoc, right_nil, list.append_nil] at hyp,
    have imposs := list.head_eq_of_cons_eq hyp,
    unfold Z at imposs,
    rw symbol.nonterminal.inj_eq at imposs,
    exact sum.no_confusion imposs,
  },
  have unn : u ≠ [],
  {
    by_contradiction u_nil,
    rw [u_nil, list.nil_append] at hyp,
    cases r₀.input_L with d l,
    {
      rw [list.map_nil, list.nil_append] at hyp,
      have imposs := list.head_eq_of_cons_eq hyp,
      have inr_eq_inl := symbol.nonterminal.inj imposs,
      exact sum.no_confusion inr_eq_inl,
    },
    {
      rw list.map_cons at hyp,
      have imposs := list.head_eq_of_cons_eq hyp,
      cases d,
      {
        unfold wrap_sym at imposs,
        exact symbol.no_confusion imposs,
      },
      {
        unfold wrap_sym at imposs,
        have inr_eq_inl := symbol.nonterminal.inj imposs,
        exact sum.no_confusion inr_eq_inl,
      },
    },
  },
  have hypr := congr_arg list.tail hyp,
  rw list.tail at hypr,
  repeat {
    rw list.append_assoc at hypr,
  },
  rw list.tail_append_of_ne_nil _ _ unn at hypr,
  repeat {
    rw ←list.append_assoc at hypr,
  },
  rcases cases_1_and_2_and_3a_match_aux is_x_nil hypr with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
  use [m, u₁, v₁],
  split,
  {
    cases u with d l,
    {
      exfalso,
      exact unn rfl,
    },
    have headZ : d = Z,
    {
      repeat {
        rw list.cons_append at hyp,
      },
      exact list.head_eq_of_cons_eq hyp.symm,
    },
    rw headZ,
    rw list.tail at u_eq,
    rw u_eq,
    apply list.cons_append,
  },
  split,
  {
    exact xm_eq,
  },
  {
    exact v_eq,
  },
end

private lemma star_case_1 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ x : list (list (symbol T g.nt)),
      (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
      (α = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) :
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))))  ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))))  :=
begin
  rcases hyp with ⟨x, valid, cat⟩,
  have no_R_in_alpha : R ∉ α,
  {
    intro contr,
    rw cat at contr,
    clear_except contr,
    rw list.mem_append at contr,
    cases contr,
    {
      rw list.mem_singleton at contr,
      exact Z_neq_R.symm contr,
    },
    {
      exact R_not_in_join_mpHmmw contr,
    },
  },
  rw cat at *,
  clear cat,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,

  cases rin,
  {
    left,
    rw rin at *,
    clear rin,
    dsimp only at *,
    rw [list.append_nil, list.append_nil] at bef,
    use ([symbol.nonterminal g.initial] :: x),
    split,
    {
      intros xᵢ xin,
      cases xin,
      {
        rw xin,
        apply grammar_deri_self,
      },
      {
        exact valid xᵢ xin,
      },
    },
    have u_nil : u = [],
    {
      clear_except bef,
      rw ←list.length_eq_zero,
      by_contradiction,
      have ul_pos : 0 < u.length,
      {
        rwa pos_iff_ne_zero,
      },
      clear h,
      have bef_tail := congr_arg list.tail bef,
      cases u with d l,
      {
        rw list.length at ul_pos,
        exact nat.lt_irrefl 0 ul_pos,
      },
      {
        have Z_in_tail : Z ∈ l ++ [symbol.nonterminal (sum.inr 0)] ++ v,
        {
          apply list.mem_append_left,
          apply list.mem_append_right,
          apply list.mem_singleton_self,
        },
        rw [list.singleton_append, list.tail_cons, list.cons_append, list.cons_append, list.tail_cons] at bef_tail,
        rw ←bef_tail at Z_in_tail,
        exact Z_not_in_join_mpHmmw Z_in_tail,
      },
    },
    have v_rest : v = list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)),
    {
      rw u_nil at bef,
      convert congr_arg list.tail bef.symm,
    },
    rw aft,
    rw [u_nil, v_rest],
    rw [list.nil_append, list.map_cons],
    refl,
  },
  cases rin,
  {
    right,
    rw rin at *,
    clear rin,
    dsimp only at *,
    rw [list.append_nil, list.append_nil] at bef,
    use x,
    split,
    {
      exact valid,
    },
    have u_nil : u = [],
    {
      clear_except bef,
      rw ←list.length_eq_zero,
      by_contradiction,
      have ul_pos : 0 < u.length,
      {
        rwa pos_iff_ne_zero,
      },
      clear h,
      have bef_tail := congr_arg list.tail bef,
      cases u with d l,
      {
        rw list.length at ul_pos,
        exact nat.lt_irrefl 0 ul_pos,
      },
      {
        have Z_in_tail : Z ∈ l ++ [symbol.nonterminal (sum.inr 0)] ++ v,
        {
          apply list.mem_append_left,
          apply list.mem_append_right,
          apply list.mem_singleton_self,
        },
        rw [list.singleton_append, list.tail_cons, list.cons_append, list.cons_append, list.tail_cons] at bef_tail,
        rw ←bef_tail at Z_in_tail,
        exact Z_not_in_join_mpHmmw Z_in_tail,
      },
    },
    have v_rest : v = list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)),
    {
      rw u_nil at bef,
      convert congr_arg list.tail bef.symm,
    },
    rw aft,
    rw [u_nil, v_rest],
    refl,
  },
  iterate 2 {
    cases rin,
    {
      exfalso,
      apply no_R_in_alpha,
      rw bef,
      apply list.mem_append_left,
      apply list.mem_append_left,
      apply list.mem_append_right,
      rw list.mem_singleton,
      rw rin,
      refl,
    },
  },
  have rin' : r ∈ rules_that_scan_terminals g ∨ r ∈ list.map wrap_gr g.rules,
  {
    rw or_comm,
    rwa ←list.mem_append,
  },
  clear rin,
  cases rin',
  {
    exfalso,
    apply no_R_in_alpha,
    rw bef,
    apply list.mem_append_left,
    apply list.mem_append_left,
    apply list.mem_append_right,
    rw list.mem_singleton,
    unfold rules_that_scan_terminals at rin',
    rw list.mem_map at rin',
    rcases rin' with ⟨t, -, form⟩,
    rw ←form,
    refl,
  },
  left,
  rw list.mem_map at rin',
  rcases rin' with ⟨r₀, orig_in, wrap_orig⟩,
  unfold wrap_gr at wrap_orig,
  rw ←wrap_orig at *,
  clear wrap_orig,
  dsimp only at *,
  rcases case_1_match_rule bef with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
  clear bef,
  rw [u_eq, v_eq] at aft,
  use (list.take m x ++ [u₁ ++ r₀.output_string ++ v₁] ++ list.drop m.succ x),
  split,
  {
    intros xᵢ xiin,
    rw list.mem_append_append at xiin,
    cases xiin,
    {
      apply valid,
      exact list.mem_of_mem_take xiin,
    },
    cases xiin,
    swap, {
      apply valid,
      exact list.mem_of_mem_drop xiin,
    },
    rw list.mem_singleton at xiin,
    rw xiin,
    have last_step :
      grammar_transforms g
        (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)
        (u₁ ++ r₀.output_string ++ v₁),
    {
      use r₀,
      split,
      {
        exact orig_in,
      },
      use [u₁, v₁],
      split;
      refl,
    },
    apply grammar_deri_of_deri_tran _ last_step,
    apply valid (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁),
    exact list.nth_mem xm_eq,
  },
  rw list.singleton_append,
  rw aft,
  repeat {
    rw list.cons_append,
  },
  apply congr_arg2,
  {
    refl,
  },
  repeat {
    rw list.map_append,
  },
  rw list.join_append_append,
  repeat {
    rw list.append_assoc,
  },
  apply congr_arg2,
  {
    rw ←list.map_take,
  },
  repeat {
    rw ←list.append_assoc,
  },
  apply congr_arg2,
  swap, {
    rw ←list.map_drop,
  },
  rw [
    list.map_singleton, list.map_singleton, list.join_singleton,
    list.map_append, list.map_append
  ],
end

private lemma uv_nil_of_RH_eq {g : grammar T} {u v : list (ns T g.nt)}
    (ass : [R, H] = u ++ [] ++ [symbol.nonterminal (sum.inr 2)] ++ [H] ++ v) :
  u = []  ∧  v = []  :=
begin
  rw list.append_nil at ass,
  have lens := congr_arg list.length ass,
  simp only [list.length_append, list.length, zero_add] at lens,
  split;
  {
    rw ←list.length_eq_zero,
    omega,
  },
end

private lemma u_nil_when_RH {g : grammar T} {x : list (list (symbol T g.nt))} {u v : list (ns T g.nt)}
    (ass :
      [R, H] ++ (list.map (++ [H]) (list.map (list.map wrap_sym) x)).join =
      u ++ [] ++ [symbol.nonterminal (sum.inr 2)] ++ [H] ++ v
    ) :
  u = []  :=
begin
  cases u with d l,
  {
    refl,
  },
  rw list.append_nil at ass,
  exfalso,
  by_cases d = R,
  {
    rw h at ass,
    clear h,
    classical,
    have imposs, { dsimp_result { exact congr_arg (λ c : list (ns T g.nt), list.count_in c R) ass } },
    repeat {
      rw list.count_in_append at imposs,
    },
    repeat {
      rw list.count_in_cons at imposs,
    },
    repeat {
      rw list.count_in_nil at imposs,
    },
    have one_imposs : 1 + (0 + 0) + 0 = 1 + list.count_in l R + (1 + 0) + (0 + 0) + list.count_in v R,
    {
      convert imposs,
      {
        norm_num,
      },
      {
        simp [H_neq_R],
      },
      {
        symmetry,
        apply zero_Rs_in_the_long_part,
      },
      {
        norm_num,
      },
      {
        simp [R],
      },
      {
        simp [H_neq_R],
      },
    },
    clear_except one_imposs,
    repeat {
      rw add_zero at one_imposs,
    },
    linarith,
  },
  {
    apply h,
    clear h,
    have impos := congr_fun (congr_arg list.nth ass) 0,
    iterate 4 {
      rw list.nth_append at impos,
      swap, {
        norm_num,
      },
    },
    rw list.nth at impos,
    rw list.nth at impos,
    exact (option.some.inj impos).symm,
  },
end

private lemma case_2_match_rule {g : grammar T} {r₀ : grule T g.nt}
    {x : list (list (symbol T g.nt))} {u v : list (ns T g.nt)}
    (hyp : R :: H :: (list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))) =
      u ++ list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        list.map wrap_sym r₀.input_R ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : list (symbol T g.nt),
    u = R :: H :: list.join (list.map (++ [H]) (list.take m (list.map (list.map wrap_sym) x))) ++ list.map wrap_sym u₁
    ∧  list.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)  ∧
    v = list.map wrap_sym v₁ ++ [H] ++
        list.join (list.map (++ [H]) (list.drop m.succ (list.map (list.map wrap_sym) x)))  :=
begin
  by_cases is_x_nil : x = [],
  {
    exfalso,
    rw [is_x_nil, list.map_nil, list.map_nil, list.join] at hyp,
    have imposs : symbol.nonterminal (sum.inl r₀.input_N) = R ∨ symbol.nonterminal (sum.inl r₀.input_N) = H,
    {
      simpa using congr_arg (λ l, symbol.nonterminal (sum.inl r₀.input_N) ∈ l) hyp,
    },
    cases imposs;
    exact sum.no_confusion (symbol.nonterminal.inj imposs),
  },
  have unn : u ≠ [],
  {
    by_contradiction u_nil,
    rw [u_nil, list.nil_append] at hyp,
    cases r₀.input_L with d l,
    {
      rw [list.map_nil, list.nil_append] at hyp,
      have imposs := list.head_eq_of_cons_eq hyp,
      have inr_eq_inl := symbol.nonterminal.inj imposs,
      exact sum.no_confusion inr_eq_inl,
    },
    {
      rw list.map_cons at hyp,
      have imposs := list.head_eq_of_cons_eq hyp,
      cases d,
      {
        unfold wrap_sym at imposs,
        exact symbol.no_confusion imposs,
      },
      {
        unfold wrap_sym at imposs,
        have inr_eq_inl := symbol.nonterminal.inj imposs,
        exact sum.no_confusion inr_eq_inl,
      },
    },
  },
  have hypt := congr_arg list.tail hyp,
  rw list.tail at hypt,
  repeat {
    rw list.append_assoc at hypt,
  },
  rw list.tail_append_of_ne_nil _ _ unn at hypt,
  have utnn : u.tail ≠ [],
  {
    by_contradiction ut_nil,
    rw [ut_nil, list.nil_append] at hypt,
    cases r₀.input_L with d l,
    {
      rw [list.map_nil, list.nil_append] at hypt,
      have imposs := list.head_eq_of_cons_eq hypt,
      have inr_eq_inl := symbol.nonterminal.inj imposs,
      exact sum.no_confusion inr_eq_inl,
    },
    {
      rw list.map_cons at hypt,
      have imposs := list.head_eq_of_cons_eq hypt,
      cases d,
      {
        unfold wrap_sym at imposs,
        exact symbol.no_confusion imposs,
      },
      {
        unfold wrap_sym at imposs,
        have inr_eq_inl := symbol.nonterminal.inj imposs,
        exact sum.no_confusion inr_eq_inl,
      },
    },
  },
  have hyptt := congr_arg list.tail hypt,
  rw list.tail at hyptt,
  rw list.tail_append_of_ne_nil _ _ utnn at hyptt,
  repeat {
    rw ←list.append_assoc at hyptt,
  },
  rcases cases_1_and_2_and_3a_match_aux is_x_nil hyptt with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
  use [m, u₁, v₁],
  split,
  {
    cases u with d l,
    {
      exfalso,
      exact unn rfl,
    },
    have headR : d = R,
    {
      repeat {
        rw list.cons_append at hyp,
      },
      exact list.head_eq_of_cons_eq hyp.symm,
    },
    rw list.tail at u_eq,
    rw list.tail at hypt,
    cases l with d' l',
    {
      exfalso,
      exact utnn rfl,
    },
    have tailHead : d' = H,
    {
      repeat {
        rw list.cons_append at hypt,
      },
      exact list.head_eq_of_cons_eq hypt.symm,
    },
    rw list.tail at u_eq,
    rw [headR, tailHead, u_eq, list.cons_append, list.cons_append],
  },
  split,
  {
    exact xm_eq,
  },
  {
    exact v_eq,
  },
end

private lemma star_case_2 {g : grammar T} {α α' : list (symbol T (star_grammar g).nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ x : list (list (symbol T g.nt)),
      (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
      (α = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) :
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))))  ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ [H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))))  ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α' = list.map symbol.terminal u)  ∨
  (∃ σ : list (symbol T g.nt), α' = list.map wrap_sym σ ++ [R])  ∨
  (∃ ω : list (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α'  :=
begin
  rcases hyp with ⟨x, valid, cat⟩,
  have no_Z_in_alpha : Z ∉ α,
  {
    intro contr,
    rw cat at contr,
    clear_except contr,
    rw list.mem_append at contr,
    cases contr,
    {
      cases contr,
      {
        exact Z_neq_R contr,
      },
      {
        apply Z_neq_H,
        rw ←list.mem_singleton,
        exact contr,
      },
    },
    {
      exact Z_not_in_join_mpHmmw contr,
    },
  },
  rw cat at *,
  clear cat,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,

  iterate 2 {
    cases rin,
    {
      exfalso,
      apply no_Z_in_alpha,
      rw bef,
      apply list.mem_append_left,
      apply list.mem_append_left,
      apply list.mem_append_right,
      rw list.mem_singleton,
      rw rin,
      refl,
    },
  },
  cases rin,
  {
    cases x with x₀ L,
    {
      right, right, right,
      rw [list.map_nil, list.map_nil, list.join, list.append_nil] at bef,
      have empty_string : u = [] ∧ v = [],
      {
        rw rin at bef,
        exact uv_nil_of_RH_eq bef,
      },
      rw [empty_string.left, list.nil_append, empty_string.right, list.append_nil] at aft,
      use list.nil,
      rw aft,
      rw [list.map_nil, list.nil_append],
      rw rin,
    },
    {
      right, left,
      use [[], [], x₀, L],
      split,
      {
        intros wᵢ wiin,
        exfalso,
        rw list.mem_nil_iff at wiin,
        exact wiin,
      },
      split,
      {
        rw [list.map_nil, list.nil_append],
        exact valid x₀ (list.mem_cons_self x₀ L),
      },
      split,
      {
        intros xᵢ xiin,
        exact valid xᵢ (list.mem_cons_of_mem x₀ xiin),
      },
      rw aft,
      rw [list.map_nil, list.append_nil, list.join, list.map_nil, list.nil_append],
      rw rin at bef ⊢,
      dsimp only at bef ⊢,
      have u_nil := u_nil_when_RH bef,
      rw [u_nil, list.nil_append] at bef ⊢,
      have eq_v := list.append_inj_right bef (by refl),
      rw ←eq_v,
      rw [list.map_cons, list.map_cons, list.join],
      rw [←list.append_assoc, ←list.append_assoc],
    },
  },
  cases rin,
  {
    cases x with x₀ L,
    {
      right, right, left,
      rw [list.map_nil, list.map_nil, list.join, list.append_nil] at bef,
      have empty_string : u = [] ∧ v = [],
      {
        rw rin at bef,
        exact uv_nil_of_RH_eq bef,
      },
      rw [empty_string.left, list.nil_append, empty_string.right, list.append_nil] at aft,
      use list.nil,
      split,
      {
        use list.nil,
        split,
        {
          refl,
        },
        {
          intros y imposs,
          exfalso,
          exact list.not_mem_nil y imposs,
        },
      },
      {
        rw aft,
        rw list.map_nil,
        rw rin,
      },
    },
    {
      right, right, right, right,
      rw rin at bef,
      dsimp only at bef,
      have u_nil := u_nil_when_RH bef,
      rw [u_nil, list.nil_append] at bef,
      have v_eq := eq.symm (list.append_inj_right bef (by refl)),
      rw [
        u_nil, list.nil_append, v_eq, rin, list.nil_append,
        list.map_cons, list.map_cons, list.join,
        list.append_assoc, list.append_join_append, ←list.append_assoc
      ] at aft,
      split,
      {
        use list.map wrap_sym x₀ ++ (list.map (λ l, [H] ++ l) (list.map (list.map wrap_sym) L)).join,
        rw aft,
        trim,
      },
      rw [list.append_assoc, ←list.append_join_append] at aft,
      rw aft,
      split;
      intro contra;
      rw list.mem_append at contra,
      {
        cases contra,
        {
          exact map_wrap_never_contains_Z contra,
        },
        cases contra,
        {
          exact Z_neq_H contra,
        },
        {
          exact Z_not_in_join_mpHmmw contra,
        },
      },
      {
        cases contra,
        {
          exact map_wrap_never_contains_R contra,
        },
        cases contra,
        {
          exact H_neq_R contra.symm,
        },
        {
          exact R_not_in_join_mpHmmw contra,
        },
      },
    },
  },
  have rin' : r ∈ rules_that_scan_terminals g ∨ r ∈ list.map wrap_gr g.rules,
  {
    rw or_comm,
    rwa ←list.mem_append,
  },
  clear rin,
  cases rin',
  {
    exfalso,
    unfold rules_that_scan_terminals at rin',
    rw list.mem_map at rin',
    rcases rin' with ⟨t, -, form⟩,
    rw ←form at bef,
    dsimp only at bef,
    rw list.append_nil at bef,
    have u_nil : u = [],
    {
      cases u with d l,
      {
        refl,
      },
      exfalso,
      repeat {
        rw list.cons_append at bef,
      },
      rw list.nil_append at bef,
      have btail := list.tail_eq_of_cons_eq bef,
      have imposs := congr_arg (λ l, R ∈ l) btail,
      dsimp only at imposs,
      apply false_of_true_eq_false,
      convert imposs.symm,
      {
        rw [eq_iff_iff, true_iff],
        apply list.mem_append_left,
        apply list.mem_append_left,
        apply list.mem_append_right,
        apply list.mem_singleton_self,
      },
      {
        rw [eq_iff_iff, false_iff],
        intro hyp,
        rw list.mem_cons_iff at hyp,
        cases hyp,
        {
          exact H_neq_R hyp.symm,
        },
        rw list.mem_join at hyp,
        rcases hyp with ⟨p, pin, Rinp⟩,
        rw list.mem_map at pin,
        rcases pin with ⟨q, qin, eq_p⟩,
        rw ←eq_p at Rinp,
        rw list.mem_append at Rinp,
        cases Rinp,
        {
          rw list.mem_map at qin,
          rcases qin with ⟨p', -, eq_q⟩,
          rw ←eq_q at Rinp,
          exact map_wrap_never_contains_R Rinp,
        },
        {
          rw list.mem_singleton at Rinp,
          exact H_neq_R Rinp.symm,
        },
      },
    },
    rw [u_nil, list.nil_append] at bef,
    have second_symbol := congr_fun (congr_arg list.nth bef) 1,
    rw list.nth_append at second_symbol,
    swap, {
      rw [list.length_cons, list.length_singleton],
      exact lt_add_one 1,
    },
    rw list.nth_append at second_symbol,
    swap, {
      rw [list.length_append, list.length_singleton, list.length_singleton],
      exact lt_add_one 1,
    },
    rw list.singleton_append at second_symbol,
    repeat {
      rw list.nth at second_symbol,
    },
    exact symbol.no_confusion (option.some.inj second_symbol),
  },
  left,
  rw list.mem_map at rin',
  rcases rin' with ⟨r₀, orig_in, wrap_orig⟩,
  unfold wrap_gr at wrap_orig,
  rw ←wrap_orig at *,
  clear wrap_orig,
  dsimp only at bef,
  rcases case_2_match_rule bef with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
  clear bef,
  rw [u_eq, v_eq] at aft,
  use (list.take m x ++ [u₁ ++ r₀.output_string ++ v₁] ++ list.drop m.succ x),
  split,
  {
    intros xᵢ xiin,
    rw list.mem_append_append at xiin,
    cases xiin,
    {
      apply valid,
      exact list.mem_of_mem_take xiin,
    },
    cases xiin,
    swap, {
      apply valid,
      exact list.mem_of_mem_drop xiin,
    },
    rw list.mem_singleton at xiin,
    rw xiin,
    have last_step :
      grammar_transforms g
        (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)
        (u₁ ++ r₀.output_string ++ v₁),
    {
      use r₀,
      split,
      {
        exact orig_in,
      },
      use [u₁, v₁],
      split;
      refl,
    },
    apply grammar_deri_of_deri_tran _ last_step,
    apply valid (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁),
    exact list.nth_mem xm_eq,
  },
  rw aft,
  repeat {
    rw list.cons_append,
  },
  apply congr_arg2,
  {
    refl,
  },
  repeat {
    rw list.map_append,
  },
  rw list.join_append_append,
  repeat {
    rw list.append_assoc,
  },
  apply congr_arg2,
  {
    refl,
  },
  rw list.nil_append,
  apply congr_arg2,
  {
    rw ←list.map_take,
    refl,
  },
  simp [list.map, list.join, list.singleton_append, list.map_append, list.append_assoc, list.map_map, list.map_drop],
end

private lemma case_3_ni_wb {g : grammar T} {w : list (list T)} {β : list T} {i : fin 3} :
  @symbol.nonterminal T (nn g.nt) (sum.inr i) ∉
    list.map (@symbol.terminal T (nn g.nt)) w.join ++ list.map (@symbol.terminal T (nn g.nt)) β  :=
begin
  intro contra,
  rw list.mem_append at contra,
  cases contra;
  {
    rw list.mem_map at contra,
    rcases contra with ⟨t, -, imposs⟩,
    exact symbol.no_confusion imposs,
  },
end

private lemma case_3_ni_u {g : grammar T}
    {w : list (list T)} {β : list T} {γ : list (symbol T g.nt)}
    {x : list (list (symbol T g.nt))} {u v : list (ns T g.nt)} {s : ns T g.nt}
    (ass :
      list.map symbol.terminal w.join ++ list.map symbol.terminal β ++ [R] ++ list.map wrap_sym γ ++ [H] ++
        (list.map (++ [H]) (list.map (list.map wrap_sym) x)).join =
      u ++ [R] ++ [s] ++ v
    ) :
  R ∉ u  :=
begin
  intro R_in_u,
  classical,
  have count_R := congr_arg (λ l, list.count_in l R) ass,
  dsimp only at count_R,
  repeat {
    rw list.count_in_append at count_R,
  },
  have R_ni_wb : R ∉ list.map symbol.terminal w.join ++ list.map symbol.terminal β,
  {
    apply @case_3_ni_wb T g,
  },
  rw list.count_in_singleton_eq at count_R,
  rw [list.count_in_singleton_neq H_neq_R, add_zero] at count_R,
  rw ←list.count_in_append at count_R,
  rw [list.count_in_zero_of_notin R_ni_wb, zero_add] at count_R,
  rw [list.count_in_zero_of_notin map_wrap_never_contains_R, add_zero] at count_R,
  rw [zero_Rs_in_the_long_part, add_zero] at count_R,
  have ucR_pos := list.count_in_pos_of_in R_in_u,
  clear_except count_R ucR_pos,
  linarith,
end

private lemma case_3_u_eq_left_side {g : grammar T}
    {w : list (list T)} {β : list T} {γ : list (symbol T g.nt)}
    {x : list (list (symbol T g.nt))} {u v : list (ns T g.nt)} {s : ns T g.nt}
    (ass :
      list.map symbol.terminal w.join ++ list.map symbol.terminal β ++ [R] ++ list.map wrap_sym γ ++ [H] ++
        list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)) =
      u ++ [symbol.nonterminal (sum.inr 2)] ++ [s] ++ v
    ) :
  u = list.map symbol.terminal w.join ++ list.map (@symbol.terminal T (nn g.nt)) β  :=
begin
  have R_ni_u : R ∉ u,
  {
    exact case_3_ni_u ass,
  },
  have R_ni_wb : R ∉ list.map symbol.terminal w.join ++ list.map symbol.terminal β,
  {
    apply @case_3_ni_wb T g,
  },
  repeat {
    rw list.append_assoc at ass,
  },
  convert congr_arg (list.take u.length) ass.symm,
  {
    rw list.take_left,
  },
  rw ←list.append_assoc,
  rw list.take_left',
  {
    classical,
    have index_of_first_R := congr_arg (list.index_of R) ass,
    rw list.index_of_append_of_notin R_ni_u at index_of_first_R,
    rw @list.singleton_append _ _ ([s] ++ v) at index_of_first_R,
    rw [←R, list.index_of_cons_self, add_zero] at index_of_first_R,
    rw [←list.append_assoc, list.index_of_append_of_notin R_ni_wb] at index_of_first_R,
    rw [list.singleton_append, list.index_of_cons_self, add_zero] at index_of_first_R,
    exact index_of_first_R,
  },
end

private lemma case_3_gamma_nil {g : grammar T}
    {w : list (list T)} {β : list T} {γ : list (symbol T g.nt)}
    {x : list (list (symbol T g.nt))} {u v : list (ns T g.nt)}
    (ass :
      list.map symbol.terminal w.join ++ list.map symbol.terminal β ++ [symbol.nonterminal (sum.inr 2)] ++
        list.map wrap_sym γ ++ [H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)) =
      u ++ [symbol.nonterminal (sum.inr 2)] ++ [H] ++ v
    ) :
  γ = []  :=
begin
  have R_ni_wb : R ∉ list.map symbol.terminal w.join ++ list.map symbol.terminal β,
  {
    apply @case_3_ni_wb T g,
  },
  have H_ni_wb : H ∉ list.map symbol.terminal w.join ++ list.map symbol.terminal β,
  {
    apply @case_3_ni_wb T g,
  },
  have H_ni_wbrg : H ∉
    list.map (@symbol.terminal T (nn g.nt)) w.join ++ list.map symbol.terminal β ++
      [symbol.nonterminal (sum.inr 2)] ++ list.map wrap_sym γ,
  {
    intro contra,
    rw list.mem_append at contra,
    cases contra,
    swap, {
      exact map_wrap_never_contains_H contra,
    },
    rw list.mem_append at contra,
    cases contra,
    {
      exact H_ni_wb contra,
    },
    {
      rw list.mem_singleton at contra,
      exact H_neq_R contra,
    },
  },
  have R_ni_u : @symbol.nonterminal T (nn g.nt) (sum.inr 2) ∉ u,
  {
    exact case_3_ni_u ass,
  },
  have H_ni_u : H ∉ u,
  {
    rw case_3_u_eq_left_side ass,
    exact H_ni_wb,
  },
  classical,
  have first_R := congr_arg (list.index_of R) ass,
  have first_H := congr_arg (list.index_of H) ass,
  repeat {
    rw list.append_assoc (list.map symbol.terminal w.join ++ list.map symbol.terminal β) at first_R,
  },
  rw list.append_assoc
    (list.map symbol.terminal w.join ++ list.map symbol.terminal β ++
      [symbol.nonterminal (sum.inr 2)] ++ list.map wrap_sym γ)
    at first_H,
  rw list.index_of_append_of_notin R_ni_wb at first_R,
  rw list.index_of_append_of_notin H_ni_wbrg at first_H,
  rw [list.cons_append, list.cons_append, list.cons_append, R, list.index_of_cons_self, add_zero] at first_R,
  rw [list.cons_append, list.index_of_cons_self, add_zero] at first_H,
  rw [list.append_assoc u, list.append_assoc u] at first_R first_H,
  rw list.index_of_append_of_notin R_ni_u at first_R,
  rw list.index_of_append_of_notin H_ni_u at first_H,
  rw [list.append_assoc _ [H], list.singleton_append, list.index_of_cons_self, add_zero] at first_R,
  rw [list.append_assoc _ [H], list.singleton_append, ←R, list.index_of_cons_ne _ H_neq_R] at first_H,
  rw [list.singleton_append, H, list.index_of_cons_self] at first_H,
  rw ←first_R at first_H,
  clear_except first_H,
  repeat {
    rw list.length_append at first_H,
  },
  rw list.length_singleton at first_H,
  rw ←add_zero ((list.map symbol.terminal w.join).length + (list.map symbol.terminal β).length + 1) at first_H,
  rw add_right_inj at first_H,
  rw list.length_map at first_H,
  rw list.length_eq_zero at first_H,
  exact first_H,
end

private lemma case_3_v_nil {g : grammar T}
    {w : list (list T)} {β : list T} {u v : list (ns T g.nt)}
    (ass :
      list.map symbol.terminal w.join ++ list.map symbol.terminal β ++ [R] ++ [H] =
      u ++ [symbol.nonterminal (sum.inr 2)] ++ [H] ++ v
    ) :
  v = []  :=
begin
  have rev := congr_arg list.reverse ass,
  repeat {
    rw list.reverse_append at rev,
  },
  repeat {
    rw list.reverse_singleton at rev,
  },
  rw ←list.reverse_eq_nil,
  cases v.reverse with d l,
  {
    refl,
  },
  exfalso,
  rw list.singleton_append at rev,
  have brt := list.tail_eq_of_cons_eq rev,
  have brtt := congr_arg list.tail brt,
  rw list.singleton_append at brtt,
  rw list.tail_cons at brtt,
  cases l with e l',
  {
    change
      (list.map symbol.terminal β).reverse ++ (list.map symbol.terminal w.join).reverse =
      [symbol.nonterminal (sum.inr 2)] ++ u.reverse
    at brtt,
    have imposs := congr_arg (λ a, R ∈ a) brtt,
    dsimp only at imposs,
    apply false_of_true_eq_false,
    convert imposs.symm,
    {
      rw [eq_iff_iff, true_iff],
      apply list.mem_append_left,
      apply list.mem_singleton_self,
    },
    {
      rw [eq_iff_iff, false_iff],
      rw list.mem_append,
      push_neg,
      split;
      {
        rw list.mem_reverse,
        rw list.mem_map,
        push_neg,
        intros t trash,
        apply symbol.no_confusion,
      },
    },
  },
  {
    change _ = _ ++ _ at brtt,
    have imposs := congr_arg (λ a, H ∈ a) brtt,
    dsimp only at imposs,
    apply false_of_true_eq_false,
    convert imposs.symm,
    {
      rw [eq_iff_iff, true_iff],
      apply list.mem_append_right,
      apply list.mem_append_left,
      apply list.mem_singleton_self,
    },
    {
      rw [eq_iff_iff, false_iff],
      rw list.mem_append,
      push_neg,
      split;
      {
        rw list.mem_reverse,
        rw list.mem_map,
        push_neg,
        intros t trash,
        apply symbol.no_confusion,
      },
    },
  },
end

private lemma case_3_false_of_wbr_eq_urz {g : grammar T} {r₀ : grule T g.nt}
    {w : list (list T)} {β : list T} {u z : list (ns T g.nt)}
    (contradictory_equality :
      list.map symbol.terminal w.join ++ list.map symbol.terminal β ++ [R] =
      u ++ list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ z) :
  false :=
begin
  apply false_of_true_eq_false,
  convert congr_arg ((∈) (symbol.nonterminal (sum.inl r₀.input_N))) contradictory_equality.symm,
  {
    rw [eq_iff_iff, true_iff],
    apply list.mem_append_left,
    apply list.mem_append_right,
    apply list.mem_singleton_self,
  },
  {
    rw [eq_iff_iff, false_iff],
    intro hyp_N_in,
    rw list.mem_append at hyp_N_in,
    cases hyp_N_in,
    swap, {
      rw list.mem_singleton at hyp_N_in,
      exact sum.no_confusion (symbol.nonterminal.inj hyp_N_in),
    },
    rw list.mem_append at hyp_N_in,
    cases hyp_N_in;
    {
      rw list.mem_map at hyp_N_in,
      rcases hyp_N_in with ⟨t, -, impos⟩,
      exact symbol.no_confusion impos,
    },
  },
end

private lemma case_3_match_rule {g : grammar T} {r₀ : grule T g.nt}
    {x : list (list (symbol T g.nt))} {u v : list (ns T g.nt)}
    {w : list (list T)} {β : list T} {γ : list (symbol T g.nt)}
    (hyp :
      list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
        list.map wrap_sym γ ++ [H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)) =
      u ++ list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        list.map wrap_sym r₀.input_R ++ v) :
  (∃ m : ℕ, ∃ u₁ v₁ : list (symbol T g.nt),
    u = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++
        [R] ++ list.map wrap_sym γ ++ [H] ++
        list.join (list.map (++ [H]) (list.take m (list.map (list.map wrap_sym) x))) ++ list.map wrap_sym u₁
    ∧  list.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)  ∧
    v = list.map wrap_sym v₁ ++ [H] ++
        list.join (list.map (++ [H]) (list.drop m.succ (list.map (list.map wrap_sym) x)))) ∨
  (∃ u₁ v₁ : list (symbol T g.nt),
    u = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++ list.map wrap_sym u₁
    ∧  γ = u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁  ∧
    v = list.map wrap_sym v₁ ++ [H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))  :=
begin
  repeat {
    rw list.append_assoc u at hyp,
  },
  rw list.append_eq_append_iff at hyp,
  cases hyp,
  {
    rcases hyp with ⟨u', u_eq, xj_eq⟩,
    left,
    repeat {
      rw ←list.append_assoc at xj_eq,
    },
    by_cases is_x_nil : x = [],
    {
      exfalso,
      rw [is_x_nil, list.map_nil, list.map_nil, list.join] at xj_eq,
      have imposs := congr_arg list.length xj_eq,
      rw list.length at imposs,
      rw list.length_append_append at imposs,
      rw list.length_append_append at imposs,
      rw list.length_singleton at imposs,
      clear_except imposs,
      linarith,
    },
    rcases cases_1_and_2_and_3a_match_aux is_x_nil xj_eq with ⟨m, u₁, v₁, u'_eq, xm_eq, v_eq⟩,
    use [m, u₁, v₁],
    split,
    {
      rw u_eq,
      rw u'_eq,
      rw ←list.append_assoc,
    },
    split,
    {
      exact xm_eq,
    },
    {
      exact v_eq,
    },
  },
  {
    rcases hyp with ⟨v', left_half, right_half⟩,
    have very_middle :
      [symbol.nonterminal (sum.inl r₀.input_N)] = list.map wrap_sym [symbol.nonterminal r₀.input_N],
    {
      rw list.map_singleton,
      refl,
    },
    cases x with x₀ xₗ,
    {
      rw [list.map_nil, list.map_nil, list.join, list.append_nil] at right_half,
      rw ←right_half at left_half,
      have backwards := congr_arg list.reverse left_half,
      clear right_half left_half,
      right,
      repeat {
        rw list.reverse_append at backwards,
      },
      rw [list.reverse_singleton, list.singleton_append] at backwards,
      rw ←list.reverse_reverse v,
      cases v.reverse with e z,
      {
        exfalso,
        rw list.nil_append at backwards,
        rw ←list.map_reverse _ r₀.input_R at backwards,
        cases r₀.input_R.reverse with d l,
        {
          rw [list.map_nil, list.nil_append] at backwards,
          rw list.reverse_singleton (symbol.nonterminal (sum.inl r₀.input_N)) at backwards,
          rw list.singleton_append at backwards,
          have imposs := list.head_eq_of_cons_eq backwards,
          exact sum.no_confusion (symbol.nonterminal.inj imposs),
        },
        {
          rw [list.map_cons, list.cons_append, list.cons_append] at backwards,
          have imposs := list.head_eq_of_cons_eq backwards,
          exact wrap_never_outputs_H imposs.symm,
        },
      },
      rw [list.cons_append, list.cons_append, list.cons.inj_eq] at backwards,
      cases backwards with He backward,
      rw ←He at *,
      clear He e,
      have forward := congr_arg list.reverse backward,
      clear backward,
      repeat {
        rw list.reverse_append at forward,
      },
      repeat {
        rw list.reverse_reverse at forward,
      },
      rw ←list.append_assoc at forward,
      rw list.append_eq_append_iff at forward,
      cases forward,
      swap, {
        exfalso,
        rcases forward with ⟨a, imposs, -⟩,
        rw list.append_assoc u at imposs,
        rw list.append_assoc _ (list.map wrap_sym r₀.input_R) at imposs,
        rw ←list.append_assoc u at imposs,
        rw ←list.append_assoc u at imposs,
        exact case_3_false_of_wbr_eq_urz imposs,
      },
      rcases forward with ⟨a', left_side, gamma_is⟩,
      repeat {
        rw ←list.append_assoc at left_side,
      },
      rw list.append_eq_append_iff at left_side,
      cases left_side,
      {
        exfalso,
        rcases left_side with ⟨a, imposs, -⟩,
        exact case_3_false_of_wbr_eq_urz imposs,
      },
      rcases left_side with ⟨c', the_left, the_a'⟩,
      rw the_a' at gamma_is,
      clear the_a' a',
      rw list.append_assoc at the_left,
      rw list.append_assoc at the_left,
      rw list.append_eq_append_iff at the_left,
      cases the_left,
      {
        exfalso,
        rcases the_left with ⟨a, -, imposs⟩,
        apply false_of_true_eq_false,
        convert congr_arg ((∈) R) imposs.symm,
        {
          rw [eq_iff_iff, true_iff],
          apply list.mem_append_right,
          apply list.mem_append_left,
          apply list.mem_singleton_self,
        },
        {
          rw [eq_iff_iff, false_iff],
          rw list.mem_append,
          push_neg,
          split,
          {
            rw list.mem_map,
            push_neg,
            intros,
            apply wrap_never_outputs_R,
          },
          {
            rw list.mem_singleton,
            intro impos,
            exact sum.no_confusion (symbol.nonterminal.inj impos),
          },
        },
      },
      rcases the_left with ⟨u₀, u_eq, rule_side⟩,
      rw u_eq at *,
      clear u_eq u,
      have zr_eq : z.reverse = list.drop (c' ++ list.map wrap_sym r₀.input_R).length (list.map wrap_sym γ),
      {
        have gamma_suffix := congr_arg (list.drop (c' ++ list.map wrap_sym r₀.input_R).length) gamma_is,
        rw list.drop_left at gamma_suffix,
        exact gamma_suffix.symm,
      },
      cases u₀ with d l,
      {
        exfalso,
        rw list.nil_append at rule_side,
        cases r₀.input_L with d l,
        {
          rw [list.map_nil, list.nil_append] at rule_side,
          have imposs := list.head_eq_of_cons_eq rule_side,
          exact sum.no_confusion (symbol.nonterminal.inj imposs),
        },
        {
          rw [list.map_cons, list.cons_append] at rule_side,
          have imposs := list.head_eq_of_cons_eq rule_side,
          exact wrap_never_outputs_R imposs.symm,
        },
      },
      rw [list.singleton_append, list.cons_append, list.cons.inj_eq] at rule_side,
      cases rule_side with Rd c'_eq,
      rw ←Rd at *,
      clear Rd d,
      rw c'_eq at gamma_is,
      use [list.take l.length γ, list.drop (c' ++ list.map wrap_sym r₀.input_R).length γ],
      split,
      {
        rw ←list.singleton_append,
        have l_from_gamma := congr_arg (list.take l.length) gamma_is,
        repeat {
          rw list.append_assoc at l_from_gamma,
        },
        rw list.take_left at l_from_gamma,
        rw list.map_take,
        rw l_from_gamma,
        rw ←list.append_assoc,
      },
      split,
      {
        rw c'_eq,
        convert_to list.take l.length γ ++ list.drop l.length γ = _,
        {
          symmetry,
          apply list.take_append_drop,
        },
        trim,
        rw zr_eq at gamma_is,
        rw c'_eq at gamma_is,
        repeat {
          rw list.append_assoc at gamma_is,
        },
        have gamma_minus_initial_l := congr_arg (list.drop l.length) gamma_is,
        rw [list.drop_left, very_middle, ←list.map_drop, ←list.map_drop] at gamma_minus_initial_l,
        repeat {
          rw ←list.map_append at gamma_minus_initial_l,
        },
        rw wrap_str_inj gamma_minus_initial_l,
        trim,
        repeat {
          rw list.length_append,
        },
        repeat {
          rw list.length_map,
        },
        repeat {
          rw list.length_append,
        },
        repeat {
          rw list.length_singleton,
        },
        repeat {
          rw add_assoc,
        },
      },
      {
        rw [list.map_nil, list.map_nil, list.join, list.append_nil],
        rw [list.reverse_cons, zr_eq],
        rw list.map_drop,
      },
    },
    by_cases is_v'_nil : v' = [],
    {
      rw [is_v'_nil, list.nil_append] at right_half,
      rw [is_v'_nil, list.append_nil] at left_half,
      left,
      use [0, [], list.drop (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length x₀],
      rw [list.map_cons, list.map_cons, list.join] at right_half,
      split,
      {
        rw [list.map_nil, list.append_nil],
        rw [list.take_zero, list.map_nil, list.join, list.append_nil],
        exact left_half.symm,
      },
      have lengths_trivi :
        list.length (
          list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ list.map wrap_sym r₀.input_R
        ) =
        list.length (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R),
      {
        rw [very_middle, ←list.map_append_append],
        apply list.length_map,
      },
      have len_rᵢ_le_len_x₀ :
        (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length ≤ (list.map wrap_sym x₀).length,
      {
        classical,
        have first_H := congr_arg (list.index_of H) right_half,
        rw [list.append_assoc _ [H], list.index_of_append_of_notin map_wrap_never_contains_H] at first_H,
        rw [list.singleton_append, list.index_of_cons_self, add_zero] at first_H,
        rw [very_middle, ←list.map_append_append, list.index_of_append_of_notin map_wrap_never_contains_H] at first_H,
        rw list.length_map at first_H,
        exact nat.le.intro first_H,
      },
      split,
      {
        rw list.nth,
        apply congr_arg,
        rw list.nil_append,
        convert_to  x₀ =
            list.take (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length x₀ ++
            list.drop (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length x₀,
        {
          trim,
          apply wrap_str_inj,
          rw list.map_append_append,
          have right_left :=
            congr_arg (list.take (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length) right_half,
          rw list.take_left' lengths_trivi at right_left,
          rw [←very_middle, right_left],
          rw list.append_assoc _ [H],
          rw list.take_append_of_le_length len_rᵢ_le_len_x₀,
          rw list.map_take,
        },
        rw list.take_append_drop,
      },
      {
        rw [list.map_cons, list.drop_one, list.tail_cons],
        have right_right :=
            congr_arg (list.drop (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length) right_half,
        rw list.drop_left' lengths_trivi at right_right,
        rw right_right,
        rw list.append_assoc _ [H],
        rw list.drop_append_of_le_length len_rᵢ_le_len_x₀,
        rw list.map_drop,
        rw list.append_assoc _ [H],
        refl,
      },
    },
    right,
    obtain ⟨z, v'_eq⟩ : ∃ z,  v' =
        list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ list.map wrap_sym r₀.input_R ++ z,
    {
      obtain ⟨v'', without_final_H⟩ : ∃ v'', v' = v'' ++ [H],
      {
        rw list.append_eq_append_iff at left_half,
        cases left_half,
        {
          rcases left_half with ⟨a', -, matters⟩,
          use list.nil,
          cases a' with d l,
          {
            rw list.nil_append at matters ⊢,
            exact matters.symm,
          },
          {
            exfalso,
            have imposs := congr_arg list.length matters,
            rw [list.length_singleton, list.length_append, list.length_cons] at imposs,
            have right_pos := length_ge_one_of_not_nil is_v'_nil,
            clear_except imposs right_pos,
            linarith,
          },
        },
        {
          rcases left_half with ⟨c', -, v_c'⟩,
          exact ⟨c', v_c'⟩,
        },
      },
      rw without_final_H at right_half,
      rw list.append_assoc v'' at right_half,
      have key_prop :
        list.length (
          list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ list.map wrap_sym r₀.input_R
        ) ≤
        v''.length,
      {
        classical,
        have first_H := congr_arg (list.index_of H) right_half,
        rw [very_middle, ←list.map_append_append, list.index_of_append_of_notin map_wrap_never_contains_H] at first_H,
        have H_not_in_v'' : H ∉ v'',
        {
          rw [without_final_H, ←list.append_assoc] at left_half,
          intro contra,
          apply false_of_true_eq_false,
          convert congr_arg ((∈) H) (list.append_right_cancel left_half).symm,
          {
            rw [eq_iff_iff, true_iff],
            exact list.mem_append_right _ contra,
          },
          {
            clear_except,
            rw [eq_iff_iff, false_iff],
            intro contr,
            iterate 3 {
              rw list.mem_append at contr,
              cases contr,
            },
            iterate 2 {
              rw list.mem_map at contr,
              rcases contr with ⟨t, -, impos⟩,
              exact symbol.no_confusion impos,
            },
            {
              rw list.mem_singleton at contr,
              exact H_neq_R contr,
            },
            {
              rw list.mem_map at contr,
              rcases contr with ⟨s, -, imposs⟩,
              exact wrap_never_outputs_H imposs,
            },
          },
        },
        rw list.index_of_append_of_notin H_not_in_v'' at first_H,
        rw [list.singleton_append, list.index_of_cons_self, add_zero] at first_H,
        rw [very_middle, ←list.map_append_append],
        exact nat.le.intro first_H,
      },
      obtain ⟨n, key_prop'⟩ := nat.le.dest key_prop,
      have right_take := congr_arg (list.take v''.length) right_half,
      rw list.take_left at right_take,
      rw ←key_prop' at right_take,
      rw list.take_append at right_take,
      use list.take n v ++ [H],
      rw without_final_H,
      rw ←right_take,
      repeat {
        rw ←list.append_assoc,
      },
    },
    rw v'_eq at right_half,
    rw list.append_assoc _ z at right_half,
    rw list.append_right_inj at right_half,
    rw v'_eq at left_half,
    obtain ⟨u₁, v₁, gamma_parts, z_eq⟩ : ∃ u₁, ∃ v₁,
      list.map wrap_sym γ =
      list.map wrap_sym u₁ ++ (
        list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ list.map wrap_sym r₀.input_R
      ) ++ list.map wrap_sym v₁  ∧
      z = list.map wrap_sym v₁ ++ [H],
    {
      repeat {
        rw ←list.append_assoc at left_half,
      },
      rw list.append_assoc _ (list.map wrap_sym γ) at left_half,
      rw list.append_assoc _ _ z at left_half,
      rw list.append_eq_append_iff at left_half,
      cases left_half,
      swap, {
        exfalso,
        rcases left_half with ⟨c', imposs, -⟩,
        exact case_3_false_of_wbr_eq_urz imposs,
      },
      rcases left_half with ⟨a', lhl, lhr⟩,
      have lhl' := congr_arg list.reverse lhl,
      repeat {
        rw list.reverse_append at lhl',
      },
      rw list.reverse_singleton at lhl',
      rw ←list.reverse_reverse a' at lhr,
      cases a'.reverse with d' l',
      {
        exfalso,
        rw list.nil_append at lhl',
        rw [list.singleton_append, list.reverse_singleton, list.singleton_append] at lhl',
        have imposs := list.head_eq_of_cons_eq lhl',
        exact sum.no_confusion (symbol.nonterminal.inj imposs),
      },
      rw list.singleton_append at lhl',
      rw list.cons_append at lhl',
      rw list.cons.inj_eq at lhl',
      cases lhl' with eq_d' lhl'',
      rw ←eq_d' at lhr,
      clear eq_d' d',
      rw ←list.append_assoc l' at lhl'',
      rw list.append_eq_append_iff at lhl'',
      cases lhl'',
      swap, {
        exfalso,
        rcases lhl'' with ⟨c'', imposs, -⟩,
        rw list.reverse_singleton at imposs,
        apply false_of_true_eq_false,
        convert congr_arg ((∈) R) imposs.symm,
        {
          rw [eq_iff_iff, true_iff],
          apply list.mem_append_left,
          apply list.mem_append_right,
          apply list.mem_singleton_self,
        },
        {
          rw [eq_iff_iff, false_iff],
          rw list.mem_reverse,
          apply map_wrap_never_contains_R,
        },
      },
      rcases lhl'' with ⟨b', lhlr', lhll'⟩,
      rw list.reverse_singleton at lhlr',
      have lhlr := congr_arg list.reverse lhlr',
      rw [list.reverse_append, list.reverse_append, list.reverse_reverse] at lhlr,
      rw [list.reverse_singleton, list.singleton_append] at lhlr,
      rw ←list.reverse_reverse b' at lhll',
      cases b'.reverse with d'' l'',
      {
        exfalso,
        rw list.nil_append at lhlr,
        cases r₀.input_L with d l,
        {
          rw list.map_nil at lhlr,
          exact list.no_confusion lhlr,
        },
        rw list.map_cons at lhlr,
        have imposs := list.head_eq_of_cons_eq lhlr,
        exact wrap_never_outputs_R imposs.symm,
      },
      rw list.cons_append at lhlr,
      rw list.cons.inj_eq at lhlr,
      cases lhlr with eq_d'' lve,
      rw ←eq_d'' at lhll',
      clear eq_d'' d'',
      have lhll := congr_arg list.reverse lhll',
      rw [list.reverse_reverse, list.reverse_append, list.reverse_reverse, list.reverse_append,
          list.reverse_reverse, list.reverse_reverse] at lhll,
      rw lhll at *,
      clear lhll u,
      rw list.reverse_cons at lhr,
      rw lve at lhr,
      use list.take l''.length γ,
      use list.drop (l''
            ++ list.map wrap_sym r₀.input_L
            ++ [symbol.nonterminal (sum.inl r₀.input_N)]
            ++ list.map wrap_sym r₀.input_R
          ).length γ,
      have z_expr :  z =
        list.map wrap_sym (
            list.drop (l''
              ++ list.map wrap_sym r₀.input_L
              ++ [symbol.nonterminal (sum.inl r₀.input_N)]
              ++ list.map wrap_sym r₀.input_R
            ).length γ
          ) ++ [H],
      {
        have lhdr :=
          congr_arg
            (list.drop (l''
              ++ list.map wrap_sym r₀.input_L
              ++ [symbol.nonterminal (sum.inl r₀.input_N)]
              ++ list.map wrap_sym r₀.input_R
            ).length) lhr,
        rw list.drop_append_of_le_length at lhdr,
        {
          rw [list.map_drop, lhdr, ←list.append_assoc, list.drop_left],
        },
        have lhr' := congr_arg list.reverse lhr,
        repeat {
          rw list.reverse_append at lhr',
        },
        rw list.reverse_singleton at lhr',
        cases z.reverse with d l,
        {
          exfalso,
          rw [list.nil_append, list.singleton_append] at lhr',
          rw ←list.map_reverse _ r₀.input_R at lhr',
          cases r₀.input_R.reverse with dᵣ lᵣ,
          {
            rw [list.map_nil, list.nil_append, list.reverse_singleton, list.singleton_append] at lhr',
            have imposs := list.head_eq_of_cons_eq lhr',
            exact sum.no_confusion (symbol.nonterminal.inj imposs),
          },
          {
            rw [list.map_cons, list.cons_append] at lhr',
            have imposs := list.head_eq_of_cons_eq lhr',
            exact wrap_never_outputs_H imposs.symm,
          },
        },
        repeat {
          rw list.length_append,
        },
        have contra_len := congr_arg list.length lhr',
        repeat {
          rw list.length_append at contra_len,
        },
        repeat {
          rw list.length_reverse at contra_len,
        },
        repeat {
          rw list.length_singleton at contra_len,
        },
        rw list.length_cons at contra_len,
        rw list.length_singleton,
        clear_except contra_len,
        linarith,
      },
      split,
      swap, {
        exact z_expr,
      },
      rw z_expr at lhr,
      have gamma_expr :  list.map wrap_sym γ =
        l'' ++ list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
          (list.map wrap_sym r₀.input_R ++
            (list.map wrap_sym
              (list.drop (l''
                ++ list.map wrap_sym r₀.input_L
                ++ [symbol.nonterminal (sum.inl r₀.input_N)]
                ++ list.map wrap_sym r₀.input_R
              ).length γ))),
      {
        repeat {
          rw ←list.append_assoc at lhr,
        },
        repeat {
          rw ←list.append_assoc,
        },
        exact list.append_right_cancel lhr,
      },
      rw gamma_expr,
      trim,
      have almost := congr_arg (list.take l''.length) gamma_expr.symm,
      repeat {
        rw list.append_assoc at almost,
      },
      rw list.take_left at almost,
      rw list.map_take,
      exact almost,
    },
    use [u₁, v₁],
    split, swap, split,
    {
      apply wrap_str_inj,
      rwa [
        very_middle, ←list.map_append_append, ←list.map_append_append,
        ←list.append_assoc, ←list.append_assoc
      ] at gamma_parts,
    },
    {
      rwa z_eq at right_half,
    },
    rw gamma_parts at left_half,
    rw list.append_assoc (list.map wrap_sym u₁) at left_half,
    rw ←list.append_assoc _ (list.map wrap_sym u₁) at left_half,
    rw list.append_assoc _ _ [H] at left_half,
    have left_left := congr_arg (list.take u.length) left_half,
    rw list.take_left at left_left,
    rw list.take_left' at left_left,
    {
      exact left_left.symm,
    },
    have lh_len := congr_arg list.length left_half,
    repeat {
      rw list.length_append at lh_len,
    },
    repeat {
      rw list.length_singleton at lh_len,
    },
    have cut_off_end : z.length = (list.map wrap_sym v₁).length + 1,
    {
      simpa using congr_arg list.length z_eq,
    },
    rw cut_off_end at lh_len,
    repeat {
      rw list.length_append,
    },
    rw list.length_singleton,
    repeat {
      rw add_assoc at lh_len,
    },
    iterate 3 {
      rw ←add_assoc at lh_len,
    },
    rwa add_left_inj at lh_len,
  },
end

private lemma star_case_3 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
      (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
      (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
      (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
      (α = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
        list.map wrap_sym γ ++ [H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) :
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ [H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))))  ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α' = list.map symbol.terminal u)  ∨
  (∃ σ : list (symbol T g.nt), α' = list.map wrap_sym σ ++ [R])  ∨
  (∃ ω : list (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α'  :=
begin
  rcases hyp with ⟨w, β, γ, x, valid_w, valid_middle, valid_x, cat⟩,
  have no_Z_in_alpha : Z ∉ α,
  {
    intro contr,
    rw cat at contr,
    clear_except contr,
    repeat {
      rw list.mem_append at contr,
    },
    iterate 5 {
      cases contr,
    },
    any_goals {
      rw list.mem_map at contr,
      rcases contr with ⟨s, -, imposs⟩,
    },
    {
      exact symbol.no_confusion imposs,
    },
    {
      exact symbol.no_confusion imposs,
    },
    {
      rw list.mem_singleton at contr,
      exact Z_neq_R contr,
    },
    {
      exact wrap_never_outputs_Z imposs,
    },
    {
      rw list.mem_singleton at contr,
      exact Z_neq_H contr,
    },
    {
      exact Z_not_in_join_mpHmmw contr,
    },
  },
  rw cat at *,
  clear cat,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,

  iterate 2 {
    cases rin,
    {
      exfalso,
      apply no_Z_in_alpha,
      rw bef,
      apply list.mem_append_left,
      apply list.mem_append_left,
      apply list.mem_append_right,
      rw list.mem_singleton,
      rw rin,
      refl,
    },
  },
  cases rin,
  {
    rw rin at bef aft,
    dsimp only at bef aft,
    rw list.append_nil at bef,
    have gamma_nil_here := case_3_gamma_nil bef,
    cases x with x₀ L,
    {
      right, right, left,
      rw [gamma_nil_here, list.map_nil, list.append_nil] at bef,
      rw [list.map_nil, list.map_nil, list.join, list.append_nil] at bef,
      have v_nil := case_3_v_nil bef,
      rw [v_nil, list.append_nil] at bef aft,
      use list.map symbol.terminal w.join ++ list.map symbol.terminal β,
      rw aft,
      have bef_minus_H := list.append_right_cancel bef,
      have bef_minus_RH := list.append_right_cancel bef_minus_H,
      rw ←bef_minus_RH,
      rw [list.map_append, list.map_map, list.map_map],
      refl,
    },
    {
      left,
      use [w ++ [β], x₀, L],
      split,
      {
        intros wᵢ wiin,
        rw list.mem_append at wiin,
        cases wiin,
        {
          exact valid_w wᵢ wiin,
        },
        {
          rw list.mem_singleton at wiin,
          rw wiin,
          rw [gamma_nil_here, list.append_nil] at valid_middle,
          exact valid_middle,
        },
      },
      split,
      {
        rw [list.map_nil, list.nil_append],
        exact valid_x x₀ (list.mem_cons_self x₀ L),
      },
      split,
      {
        intros xᵢ xiin,
        exact valid_x xᵢ (list.mem_cons_of_mem x₀ xiin),
      },
      rw [list.map_nil, list.append_nil],
      rw aft,
      have u_eq : u = list.map (@symbol.terminal T (nn g.nt)) w.join ++ list.map (@symbol.terminal T (nn g.nt)) β,
      {
        exact case_3_u_eq_left_side bef,
      },
      have v_eq : v = list.join (list.map (++ [H]) (list.map (list.map wrap_sym) (x₀ :: L))),
      {
        rw u_eq at bef,
        rw [gamma_nil_here, list.map_nil, list.append_nil] at bef,
        exact (list.append_left_cancel bef).symm,
      },
      rw [u_eq, v_eq],
      rw [list.join_append, list.map_append, list.join_singleton],
      rw [list.map_cons, list.map_cons, list.join],
      rw [←list.append_assoc, ←list.append_assoc],
      refl,
    },
  },
  cases rin,
  {
    rw rin at bef aft,
    dsimp only at bef aft,
    rw list.append_nil at bef aft,
    have gamma_nil_here := case_3_gamma_nil bef,
    rw ←list.reverse_reverse x at *,
    cases x.reverse with xₘ L,
    {
      right, left,
      rw [gamma_nil_here, list.map_nil, list.append_nil] at bef,
      rw [list.reverse_nil, list.map_nil, list.map_nil, list.join, list.append_nil] at bef,
      have v_nil := case_3_v_nil bef,
      rw [v_nil, list.append_nil] at bef aft,
      use list.join w ++ β,
      split,
      {
        use w ++ [β],
        split,
        {
          rw list.join_append,
          rw list.join_singleton,
        },
        {
          intros y y_in,
          rw list.mem_append at y_in,
          cases y_in,
          {
            exact valid_w y y_in,
          },
          {
            rw list.mem_singleton at y_in,
            rw y_in,
            rw [gamma_nil_here, list.append_nil] at valid_middle,
            exact valid_middle,
          },
        },
      },
      {
        rw aft,
        have bef_minus_H := list.append_right_cancel bef,
        have bef_minus_RH := list.append_right_cancel bef_minus_H,
        rw ←bef_minus_RH,
        rw list.map_append,
      },
    },
    {
      right, right, right,
      rw list.reverse_cons at bef,
      rw aft,
      have Z_ni_wb : Z ∉ list.map (@symbol.terminal T (nn g.nt)) w.join ++ list.map symbol.terminal β,
      {
        apply case_3_ni_wb,
      },
      have R_ni_wb : R ∉ list.map (@symbol.terminal T (nn g.nt)) w.join ++ list.map symbol.terminal β,
      {
        apply case_3_ni_wb,
      },
      have u_eq : u = list.map (@symbol.terminal T (nn g.nt)) w.join ++ list.map symbol.terminal β,
      {
        exact case_3_u_eq_left_side bef,
      },
      have v_eq : v = list.join (list.map (++ [H]) (list.map (list.map wrap_sym) (L.reverse ++ [xₘ]))),
      {
        rw u_eq at bef,
        rw [gamma_nil_here, list.map_nil, list.append_nil] at bef,
        exact (list.append_left_cancel bef).symm,
      },
      rw [u_eq, v_eq],
      split,
      {
        use list.map symbol.terminal w.join ++ list.map symbol.terminal β ++
            list.join (list.map (++ [H]) (list.map (list.map wrap_sym) L.reverse)) ++ list.map wrap_sym xₘ,
        rw [
          list.map_append, list.map_append, list.join_append,
          list.map_singleton, list.map_singleton, list.join_singleton,
          ←list.append_assoc, ←list.append_assoc
        ], refl,
      },
      split,
      {
        intro contra,
        rw list.mem_append at contra,
        cases contra,
        {
          exact Z_ni_wb contra,
        },
        {
          exact Z_not_in_join_mpHmmw contra,
        },
      },
      {
        intro contra,
        rw list.mem_append at contra,
        cases contra,
        {
          exact R_ni_wb contra,
        },
        {
          exact R_not_in_join_mpHmmw contra,
        },
      },
    },
  },
  have rin' : r ∈ rules_that_scan_terminals g ∨ r ∈ list.map wrap_gr g.rules,
  {
    rw or_comm,
    rwa ←list.mem_append,
  },
  clear rin,
  cases rin',
  {
    left,
    unfold rules_that_scan_terminals at rin',
    rw list.mem_map at rin',
    rcases rin' with ⟨t, -, r_is⟩,
    rw ←r_is at bef aft,
    dsimp only at bef aft,
    rw list.append_nil at bef,
    have u_matches : u = list.map (@symbol.terminal T (nn g.nt)) w.join ++ list.map symbol.terminal β,
    {
      exact case_3_u_eq_left_side bef,
    },
    have tv_matches :
      [symbol.terminal t] ++ v =
      list.map wrap_sym γ ++ [H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)),
    {
      rw u_matches at bef,
      repeat {
        rw list.append_assoc at bef,
      },
      have almost := list.append_left_cancel (list.append_left_cancel (list.append_left_cancel bef)),
      rw ←list.append_assoc at almost,
      exact almost.symm,
    },
    cases γ with a δ,
    {
      exfalso,
      rw [list.map_nil, list.nil_append, list.singleton_append, list.singleton_append] at tv_matches,
      have t_matches := list.head_eq_of_cons_eq tv_matches,
      exact symbol.no_confusion t_matches,
    },
    rw [list.singleton_append, list.map_cons, list.cons_append, list.cons_append] at tv_matches,
    use [w, β ++ [t], δ, x],
    split,
    {
      exact valid_w,
    },
    split,
    {
      have t_matches' := list.head_eq_of_cons_eq tv_matches,
      cases a;
      unfold wrap_sym at t_matches',
      {
        have t_eq_a := symbol.terminal.inj t_matches',
        rw [t_eq_a, list.map_append, list.map_singleton, list.append_assoc, list.singleton_append],
        exact valid_middle,
      },
      {
        exfalso,
        exact symbol.no_confusion t_matches',
      },
    },
    split,
    {
      exact valid_x,
    },
    rw aft,
    rw u_matches,
    rw [list.map_append, list.map_singleton],
    have v_matches := list.tail_eq_of_cons_eq tv_matches,
    rw v_matches,
    simp [list.append_assoc],
  },
  left,
  rw list.mem_map at rin',
  rcases rin' with ⟨r₀, orig_in, wrap_orig⟩,
  unfold wrap_gr at wrap_orig,
  rw ←wrap_orig at *,
  clear wrap_orig,
  cases case_3_match_rule bef,
  {
    rcases h with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
    clear bef,
    dsimp only at aft,
    rw [u_eq, v_eq] at aft,
    use w,
    use β,
    use γ,
    use (list.take m x ++ [u₁ ++ r₀.output_string ++ v₁] ++ list.drop m.succ x),
    split,
    {
      exact valid_w,
    },
    split,
    {
      exact valid_middle,
    },
    split,
    {
      intros xᵢ xiin,
      rw list.mem_append_append at xiin,
      cases xiin,
      {
        apply valid_x,
        exact list.mem_of_mem_take xiin,
      },
      cases xiin,
      swap, {
        apply valid_x,
        exact list.mem_of_mem_drop xiin,
      },
      {
        rw list.mem_singleton at xiin,
        rw xiin,
        have last_step :
          grammar_transforms g
            (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)
            (u₁ ++ r₀.output_string ++ v₁),
        {
          use r₀,
          split,
          {
            exact orig_in,
          },
          use [u₁, v₁],
          split;
          refl,
        },
        apply grammar_deri_of_deri_tran _ last_step,
        apply valid_x (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁),
        exact list.nth_mem xm_eq,
      },
    },
    {
      rw aft,
      trim,
      rw [
        list.map_append_append,
        list.map_append_append,
        list.join_append_append,
        ←list.map_take,
        ←list.map_drop,
        list.map_singleton,
        list.map_singleton,
        list.join_singleton,
        list.map_append_append,
        ←list.append_assoc,
        ←list.append_assoc,
        ←list.append_assoc
      ],
    },
  },
  {
    rcases h with ⟨u₁, v₁, u_eq, γ_eq, v_eq⟩,
    clear bef,
    dsimp only at aft,
    rw [u_eq, v_eq] at aft,
    use w,
    use β,
    use u₁ ++ r₀.output_string ++ v₁,
    use x,
    split,
    {
      exact valid_w,
    },
    split,
    {
      apply grammar_deri_of_deri_tran valid_middle,
      rw γ_eq,
      use r₀,
      split,
      {
        exact orig_in,
      },
      use [list.map symbol.terminal β ++ u₁, v₁],
      split,
      repeat {
        rw ←list.append_assoc,
      },
    },
    split,
    {
      exact valid_x,
    },
    {
      rw aft,
      trim,
      rw list.map_append_append,
    },
  },
end

private lemma star_case_4 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ u : list T, u ∈ (grammar_language g).star ∧ α = list.map symbol.terminal u) :
  false :=
begin
  rcases hyp with ⟨w, -, alpha_of_w⟩,
  rw alpha_of_w at orig,
  rcases orig with ⟨r, -, u, v, bef, -⟩,
  simpa using congr_arg (λ l, symbol.nonterminal r.input_N ∈ l) bef,
end

private lemma star_case_5 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ σ : list (symbol T g.nt), α = list.map wrap_sym σ ++ [R]) :
  (∃ σ : list (symbol T g.nt), α' = list.map wrap_sym σ ++ [R])  :=
begin
  rcases hyp with ⟨w, ends_with_R⟩,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,
  rw ends_with_R at bef,
  clear ends_with_R,
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      simp only [list.append_nil] at bef,
      have imposs := congr_arg (λ l, Z ∈ l) bef,
      simp only [list.mem_append] at imposs,
      rw list.mem_singleton at imposs,
      rw list.mem_singleton at imposs,
      apply false_of_true_eq_false,
      convert imposs.symm,
      {
        unfold Z,
        rw [eq_self_iff_true, or_true, true_or],
      },
      {
        rw [eq_iff_iff, false_iff],
        push_neg,
        split,
        {
          apply map_wrap_never_contains_Z,
        },
        {
          exact Z_neq_R,
        },
      },
    },
  },
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      dsimp only at bef,
      rw list.append_nil at bef,
      have rev := congr_arg list.reverse bef,
      repeat {
        rw list.reverse_append at rev,
      },
      repeat {
        rw list.reverse_singleton at rev,
      },
      rw list.singleton_append at rev,
      cases v.reverse with d l,
      {
        rw list.nil_append at rev,
        rw list.singleton_append at rev,
        have tails := list.tail_eq_of_cons_eq rev,
        rw ←list.map_reverse at tails,
        cases w.reverse with d' l',
        {
          rw list.map_nil at tails,
          have imposs := congr_arg list.length tails,
          rw [list.length, list.length_append, list.length_singleton] at imposs,
          clear_except imposs,
          linarith,
        },
        {
          rw list.map_cons at tails,
          rw list.singleton_append at tails,
          have heads := list.head_eq_of_cons_eq tails,
          exact wrap_never_outputs_R heads,
        },
      },
      {
        have tails := list.tail_eq_of_cons_eq rev,
        have H_in_tails := congr_arg (λ l, H ∈ l) tails,
        dsimp only at H_in_tails,
        rw list.mem_reverse at H_in_tails,
        apply false_of_true_eq_false,
        convert H_in_tails.symm,
        {
          rw [eq_iff_iff, true_iff],
          apply list.mem_append_right,
          apply list.mem_append_left,
          apply list.mem_singleton_self,
        },
        {
          rw [eq_iff_iff, false_iff],
          intro hyp_H_in,
          exact map_wrap_never_contains_H hyp_H_in,
        },
      },
    },
  },
  change r ∈ list.map wrap_gr g.rules ++ rules_that_scan_terminals g at rin,
  rw list.mem_append at rin,
  cases rin,
  {
    rw list.mem_map at rin,
    rcases rin with ⟨r₀, -, r_of_r₀⟩,
    rw list.append_eq_append_iff at bef,
    cases bef,
    {
      rcases bef with ⟨x, ur_eq, singleR⟩,
      by_cases is_x_nil : x = [],
      {
        have v_is_R : v = [R],
        {
          rw [is_x_nil, list.nil_append] at singleR,
          exact singleR.symm,
        },
        rw v_is_R at aft,
        rw [is_x_nil, list.append_nil] at ur_eq,
        have u_from_w : u = list.take u.length (list.map wrap_sym w),
        { -- do not extract out of `cases bef`
          repeat {
            rw list.append_assoc at ur_eq,
          },
          have tak := congr_arg (list.take u.length) ur_eq,
          rw list.take_left at tak,
          exact tak,
        },
        rw ←list.map_take at u_from_w,
        rw u_from_w at aft,
        rw ←r_of_r₀ at aft,
        dsimp only [wrap_gr] at aft,
        use list.take u.length w ++ r₀.output_string,
        rw list.map_append,
        exact aft,
      },
      {
        exfalso,
        have x_is_R : x = [R],
        {
          by_cases is_v_nil : v = [],
          {
            rw [is_v_nil, list.append_nil] at singleR,
            exact singleR.symm,
          },
          {
            exfalso,
            have imposs := congr_arg list.length singleR,
            rw list.length_singleton at imposs,
            rw list.length_append at imposs,
            have xl_ge_one := length_ge_one_of_not_nil is_x_nil,
            have vl_ge_one := length_ge_one_of_not_nil is_v_nil,
            clear_except imposs xl_ge_one vl_ge_one,
            linarith,
          },
        },
        rw x_is_R at ur_eq,
        have ru_eq := congr_arg list.reverse ur_eq,
        repeat {
          rw list.reverse_append at ru_eq,
        },
        repeat {
          rw list.reverse_singleton at ru_eq,
          rw list.singleton_append at ru_eq,
        },
        rw ←r_of_r₀ at ru_eq,
        dsimp only [wrap_gr, R] at ru_eq,
        rw ←list.map_reverse at ru_eq,
        cases r₀.input_R.reverse with d l,
        {
          rw [list.map_nil, list.nil_append] at ru_eq,
          have imposs := list.head_eq_of_cons_eq ru_eq,
          exact sum.no_confusion (symbol.nonterminal.inj imposs),
        },
        {
          have imposs := list.head_eq_of_cons_eq ru_eq,
          cases d;
          unfold wrap_sym at imposs,
          {
            exact symbol.no_confusion imposs,
          },
          {
            exact sum.no_confusion (symbol.nonterminal.inj imposs),
          },
        },
      },
    },
    {
      rcases bef with ⟨y, w_eq, v_eq⟩,
      have u_from_w : u = list.take u.length (list.map wrap_sym w),
      { -- do not extract out of `cases bef`
        repeat {
          rw list.append_assoc at w_eq,
        },
        have tak := congr_arg (list.take u.length) w_eq,
        rw list.take_left at tak,
        exact tak.symm,
      },
      have y_from_w :
        y = list.drop (u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R).length (list.map wrap_sym w),
      {
        have drp := congr_arg (list.drop (u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R).length) w_eq,
        rw list.drop_left at drp,
        exact drp.symm,
      },
      -- weird that `u_from_w` and `y_from_w` did not unify their type parameters in the same way
      rw u_from_w at aft,
      rw y_from_w at v_eq,
      rw v_eq at aft,
      use list.take u.length w ++ r₀.output_string ++
          list.drop (u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R).length w,
      rw list.map_append_append,
      rw list.map_take,
      rw list.map_drop,
      rw aft,
      trim, -- fails to identify `list.take u.length (list.map wrap_sym w)` of defin-equal type parameters
      rw ←r_of_r₀,
      dsimp only [wrap_gr],
      refl, -- outside level `(symbol T (star_grammar g).nt) = (ns T g.nt) = (symbol T (nn g.nt))`
    },
  },
  {
    exfalso,
    unfold rules_that_scan_terminals at rin,
    rw list.mem_map at rin,
    rcases rin with ⟨t, -, eq_r⟩,
    rw ←eq_r at bef,
    clear eq_r,
    dsimp only at bef,
    rw list.append_nil at bef,
    have rev := congr_arg list.reverse bef,
    repeat {
      rw list.reverse_append at rev,
    },
    repeat {
      rw list.reverse_singleton at rev,
    },
    rw list.singleton_append at rev,
    cases v.reverse with d l,
    {
      rw list.nil_append at rev,
      rw list.singleton_append at rev,
      have tails := list.tail_eq_of_cons_eq rev,
      rw ←list.map_reverse at tails,
      cases w.reverse with d' l',
      {
        rw list.map_nil at tails,
        have imposs := congr_arg list.length tails,
        rw [list.length, list.length_append, list.length_singleton] at imposs,
        clear_except imposs,
        linarith,
      },
      {
        rw list.map_cons at tails,
        rw list.singleton_append at tails,
        have heads := list.head_eq_of_cons_eq tails,
        exact wrap_never_outputs_R heads,
      },
    },
    {
      have tails := list.tail_eq_of_cons_eq rev,
      have R_in_tails := congr_arg (λ l, R ∈ l) tails,
      dsimp only at R_in_tails,
      rw list.mem_reverse at R_in_tails,
      apply false_of_true_eq_false,
      convert R_in_tails.symm,
      {
        rw [eq_iff_iff, true_iff],
        apply list.mem_append_right,
        apply list.mem_append_right,
        apply list.mem_append_left,
        apply list.mem_singleton_self,
      },
      {
        rw [eq_iff_iff, false_iff],
        intro hyp_R_in,
        exact map_wrap_never_contains_R hyp_R_in,
      },
    },
  },
end

private lemma star_case_6 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : (∃ ω : list (ns T g.nt), α = ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α) :
  (∃ ω : list (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α'  :=
begin
  rcases hyp with ⟨⟨w, ends_with_H⟩, no_Z, no_R⟩,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      simp only [list.append_nil] at bef,
      rw bef at no_Z,
      apply no_Z,
      apply list.mem_append_left,
      apply list.mem_append_right,
      apply list.mem_singleton_self,
    },
  },
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      dsimp only at bef,
      rw list.append_nil at bef,
      rw bef at no_R,
      apply no_R,
      apply list.mem_append_left,
      apply list.mem_append_left,
      apply list.mem_append_right,
      apply list.mem_singleton_self,
    },
  },
  change r ∈ list.map wrap_gr g.rules ++ rules_that_scan_terminals g at rin,
  rw list.mem_append at rin,
  cases rin,
  {
    rw ends_with_H at bef,
    rw list.mem_map at rin,
    rcases rin with ⟨r₀, -, r_of_r₀⟩,
    split,
    swap, {
      split,
      {
        rw aft,
        intro contra,
        rw list.mem_append at contra,
        rw list.mem_append at contra,
        cases contra,
        swap, {
          apply no_Z,
          rw ends_with_H,
          rw bef,
          rw list.mem_append,
          right,
          exact contra,
        },
        cases contra,
        {
          apply no_Z,
          rw ends_with_H,
          rw bef,
          repeat {
            rw list.append_assoc,
          },
          rw list.mem_append,
          left,
          exact contra,
        },
        rw ←r_of_r₀ at contra,
        unfold wrap_gr at contra,
        rw list.mem_map at contra,
        rcases contra with ⟨s, -, imposs⟩,
        cases s,
        {
          unfold wrap_sym at imposs,
          exact symbol.no_confusion imposs,
        },
        {
          unfold wrap_sym at imposs,
          unfold Z at imposs,
          rw symbol.nonterminal.inj_eq at imposs,
          exact sum.no_confusion imposs,
        },
      },
      {
        rw aft,
        intro contra,
        rw list.mem_append at contra,
        rw list.mem_append at contra,
        cases contra,
        swap, {
          apply no_R,
          rw ends_with_H,
          rw bef,
          rw list.mem_append,
          right,
          exact contra,
        },
        cases contra,
        {
          apply no_R,
          rw ends_with_H,
          rw bef,
          repeat {
            rw list.append_assoc,
          },
          rw list.mem_append,
          left,
          exact contra,
        },
        rw ←r_of_r₀ at contra,
        unfold wrap_gr at contra,
        rw list.mem_map at contra,
        rcases contra with ⟨s, -, imposs⟩,
        cases s,
        {
          unfold wrap_sym at imposs,
          exact symbol.no_confusion imposs,
        },
        {
          unfold wrap_sym at imposs,
          unfold R at imposs,
          rw symbol.nonterminal.inj_eq at imposs,
          exact sum.no_confusion imposs,
        },
      },
    },
    use u ++ r.output_string ++ v.take (v.length - 1),
    rw aft,
    trim,
    have vlnn : v.length ≥ 1,
    {
      by_contradiction contra,
      have v_nil := zero_of_not_ge_one contra,
      rw list.length_eq_zero at v_nil,
      rw v_nil at bef,
      rw ←r_of_r₀ at bef,
      rw list.append_nil at bef,
      unfold wrap_gr at bef,
      have rev := congr_arg list.reverse bef,
      clear_except rev,
      repeat {
        rw list.reverse_append at rev,
      },
      rw ←list.map_reverse _ r₀.input_R at rev,
      rw list.reverse_singleton at rev,
      cases r₀.input_R.reverse with d l,
      {
        have H_eq_N : H = symbol.nonterminal (sum.inl r₀.input_N),
        {
          rw [list.map_nil, list.nil_append,
            list.reverse_singleton, list.singleton_append, list.singleton_append,
            list.cons.inj_eq] at rev,
          exact rev.left,
        },
        unfold H at H_eq_N,
        have inr_eq_inl := symbol.nonterminal.inj H_eq_N,
        exact sum.no_confusion inr_eq_inl,
      },
      {
        rw list.map_cons at rev,
        have H_is : H = wrap_sym d,
        {
          rw [list.singleton_append, list.cons_append, list.cons.inj_eq] at rev,
          exact rev.left,
        },
        unfold H at H_is,
        cases d;
        unfold wrap_sym at H_is,
        {
          exact symbol.no_confusion H_is,
        },
        {
          rw symbol.nonterminal.inj_eq at H_is,
          exact sum.no_confusion H_is,
        },
      },
    },
    convert_to list.take (v.length - 1) v ++ list.drop (v.length - 1) v = list.take (v.length - 1) v ++ [H],
    {
      rw list.take_append_drop,
    },
    trim,
    have bef_rev := congr_arg list.reverse bef,
    repeat {
      rw list.reverse_append at bef_rev,
    },
    have bef_rev_tak := congr_arg (list.take 1) bef_rev,
    rw list.take_left' at bef_rev_tak,
    swap, {
      rw list.length_reverse,
      apply list.length_singleton,
    },
    rw list.take_append_of_le_length at bef_rev_tak,
    swap, {
      rw list.length_reverse,
      exact vlnn,
    },
    rw list.reverse_take _ vlnn at bef_rev_tak,
    rw list.reverse_eq_iff at bef_rev_tak,
    rw list.reverse_reverse at bef_rev_tak,
    exact bef_rev_tak.symm,
  },
  {
    exfalso,
    unfold rules_that_scan_terminals at rin,
    rw list.mem_map at rin,
    rcases rin with ⟨t, -, eq_r⟩,
    rw ←eq_r at bef,
    dsimp only at bef,
    rw list.append_nil at bef,
    rw bef at no_R,
    apply no_R,
    apply list.mem_append_left,
    apply list.mem_append_left,
    apply list.mem_append_right,
    apply list.mem_singleton_self,
  },
end

private lemma star_induction {g : grammar T} {α : list (ns T g.nt)}
    (ass : grammar_derives (star_grammar g) [Z] α) :
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))))  ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))))  ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ [H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))))  ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α = list.map symbol.terminal u)  ∨
  (∃ σ : list (symbol T g.nt), α = list.map wrap_sym σ ++ [R])  ∨
  (∃ ω : list (ns T g.nt), α = ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α  :=
begin
  induction ass with a b trash orig ih,
  {
    left,
    use list.nil,
    split,
    {
      intros y imposs,
      exfalso,
      exact list.not_mem_nil y imposs,
    },
    {
      refl,
    },
  },
  cases ih,
  {
    rw ←or_assoc,
    left,
    exact star_case_1 orig ih,
  },
  cases ih,
  {
    right,
    exact star_case_2 orig ih,
  },
  cases ih,
  {
    right, right,
    exact star_case_3 orig ih,
  },
  cases ih,
  {
    exfalso,
    exact star_case_4 orig ih,
  },
  cases ih,
  {
    right, right, right, right, left,
    exact star_case_5 orig ih,
  },
  {
    right, right, right, right, right,
    exact star_case_6 orig ih,
  },
end

end hard_direction


/-- The class of type-0 languages is closed under the Kleene star. -/
theorem T0_of_star_T0 (L : language T) :
  is_T0 L  →  is_T0 L.star  :=
begin
  rintro ⟨g, hg⟩,
  use star_grammar g,

  apply set.eq_of_subset_of_subset,
  {
    -- prove `L.star ⊇` here
    intros w hyp,
    unfold grammar_language at hyp,
    rw set.mem_set_of_eq at hyp,
    have result := star_induction hyp,
    clear hyp,
    cases result,
    {
      exfalso,
      rcases result with ⟨x, -, contr⟩,
      cases w with d l,
      {
        tauto,
      },
      rw list.map_cons at contr,
      have terminal_eq_Z : symbol.terminal d = Z,
      {
        exact list.head_eq_of_cons_eq contr,
      },
      exact symbol.no_confusion terminal_eq_Z,
    },
    cases result,
    {
      exfalso,
      rcases result with ⟨x, -, contr⟩,
      cases w with d l,
      {
        tauto,
      },
      rw list.map_cons at contr,
      have terminal_eq_R : symbol.terminal d = R,
      {
        exact list.head_eq_of_cons_eq contr,
      },
      exact symbol.no_confusion terminal_eq_R,
    },
    cases result,
    {
      exfalso,
      rcases result with ⟨α, β, γ, x, -, -, -, contr⟩,
      have output_contains_R : R ∈ list.map symbol.terminal w,
      {
        rw contr,
        apply list.mem_append_left,
        apply list.mem_append_left,
        apply list.mem_append_left,
        apply list.mem_append_right,
        apply list.mem_cons_self,
      },
      rw list.mem_map at output_contains_R,
      rcases output_contains_R with ⟨t, -, terminal_eq_R⟩,
      exact symbol.no_confusion terminal_eq_R,
    },
    cases result,
    {
      rcases result with ⟨u, win, map_eq_map⟩,
      have w_eq_u : w = u,
      {
        have st_inj : function.injective (@symbol.terminal T (star_grammar g).nt),
        {
          apply symbol.terminal.inj,
        },
        rw ←list.map_injective_iff at st_inj,
        exact st_inj map_eq_map,
      },
      rw [w_eq_u, ←hg],
      exact win,
    },
    cases result,
    {
      exfalso,
      cases result with σ contr,
      have last_symbols := congr_fun (congr_arg list.nth (congr_arg list.reverse contr)) 0,
      rw [
        ←list.map_reverse,
        list.reverse_append,
        list.reverse_singleton,
        list.singleton_append,
        list.nth,
        list.nth_map
      ] at last_symbols,
      cases w.reverse.nth 0,
      {
        rw option.map_none' at last_symbols,
        exact option.no_confusion last_symbols,
      },
      {
        rw option.map_some' at last_symbols,
        have terminal_eq_R := option.some.inj last_symbols,
        exact symbol.no_confusion terminal_eq_R,
      },
    },
    {
      exfalso,
      rcases result with ⟨⟨ω, contr⟩, -⟩,
      have last_symbols := congr_fun (congr_arg list.nth (congr_arg list.reverse contr)) 0,
      rw [
        ←list.map_reverse,
        list.reverse_append,
        list.reverse_singleton,
        list.singleton_append,
        list.nth,
        list.nth_map
      ] at last_symbols,
      cases w.reverse.nth 0,
      {
        rw option.map_none' at last_symbols,
        exact option.no_confusion last_symbols,
      },
      {
        rw option.map_some' at last_symbols,
        have terminal_eq_H := option.some.inj last_symbols,
        exact symbol.no_confusion terminal_eq_H,
      },
    },
  },
  {
    -- prove `L.star ⊆` here
    intros p ass,
    unfold grammar_language,
    rw language.star at ass,
    rw set.mem_set_of_eq at ⊢ ass,
    rcases ass with ⟨w, w_join, parts_in_L⟩,
    let v := w.reverse,
    have v_reverse : v.reverse = w,
    {
      apply list.reverse_reverse,
    },
    rw ←v_reverse at *,
    rw w_join,
    clear w_join p,
    unfold grammar_generates,
    rw ←hg at parts_in_L,
    cases short_induction parts_in_L with derived terminated,
    apply grammar_deri_of_deri_deri derived,
    apply grammar_deri_of_tran_deri,
    {
      use (star_grammar g).rules.nth_le 1 (by dec_trivial),
      split,
      {
        apply list.nth_le_mem,
      },
      use [[], (list.map (++ [H]) (list.map (list.map symbol.terminal) v.reverse)).join],
      split,
      {
        rw list.reverse_reverse,
        refl,
      },
      {
        refl, -- binds the implicit argument of `grammar_deri_of_tran_deri`
      },
    },
    rw list.nil_append,
    rw v_reverse,
    have final_step :
      grammar_transforms (star_grammar g)
        (list.map symbol.terminal w.join ++ [R, H])
        (list.map symbol.terminal w.join),
    {
      use (star_grammar g).rules.nth_le 3 (by dec_trivial),
      split_ile,
      use [list.map symbol.terminal w.join, list.nil],
      split,
      {
        trim,
      },
      {
        have out_nil : ((star_grammar g).rules.nth_le 3 _).output_string = [],
        {
          refl,
        },
        rw [list.append_nil, out_nil, list.append_nil],
      },
    },
    apply grammar_deri_of_deri_tran _ final_step,
    convert_to
      grammar_derives (star_grammar g)
        ([R] ++ ([H] ++ (list.map (++ [H]) (list.map (list.map symbol.terminal) w)).join))
        (list.map symbol.terminal w.join ++ [R, H]),
    have rebracket :
      [H] ++ (list.map (++ [H]) (list.map (list.map symbol.terminal) w)).join =
      (list.map (λ v, [H] ++ v) (list.map (list.map symbol.terminal) w)).join ++ [H],
    {
      apply list.append_join_append,
    },
    rw rebracket,
    apply terminal_scan_aux,
    intros v vin t tin,
    rw ←list.mem_reverse at vin,
    exact terminated v vin t tin,
  },
end
