import unrestricted.grammarLiftSink
import unrestricted.closure_properties.binary.RE_concatenation_RE


-- new nonterminal type
private def nn (N : Type) : Type :=
N ⊕ fin 3

-- new symbol type
private def ns (T N : Type) : Type :=
symbol T (nn N)

variables {T : Type}


section specific_symbols

private def Z {N : Type} : ns T N := symbol.nonterminal (sum.inr 0)
private def H {N : Type} : ns T N := symbol.nonterminal (sum.inr 1) -- originally denoted by `#`
private def R {N : Type} : ns T N := symbol.nonterminal (sum.inr 2)

private def S {g : grammar T} : ns T g.nt := symbol.nonterminal (sum.inl g.initial)

private lemma Z_neq_H {N : Type} : Z ≠ @H T N :=
begin
  intro ass,
  have imposs := sum.inr.inj (symbol.nonterminal.inj ass),
  exact fin.zero_ne_one imposs,
end

private lemma R_neq_Z {N : Type} : R ≠ @Z T N :=
begin
  intro ass,
  have imposs := sum.inr.inj (symbol.nonterminal.inj ass),
  have : (2 : fin 3) ≠ (0 : fin 3), dec_trivial,
  exact this imposs,
end

private lemma R_neq_H {N : Type} : R ≠ @H T N :=
begin
  intro ass,
  have imposs := sum.inr.inj (symbol.nonterminal.inj ass),
  have : (2 : fin 3) ≠ (1 : fin 3), dec_trivial,
  exact this imposs,
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



section hard_direction

lemma zero_of_not_ge_one {n : ℕ} (not_pos : ¬ (n ≥ 1)) : n = 0 :=
begin
  push_neg at not_pos,
  rwa nat.lt_one_iff at not_pos,
end

private lemma wrap_never_outputs_Z {N : Type} {a : symbol T N} :
  wrap_sym a ≠ Z :=
begin
  unfold Z,
  cases a;
  unfold wrap_sym,
  {
    apply symbol.no_confusion,
  },
  intro contr,
  have inl_eq_inr := symbol.nonterminal.inj contr,
  exact sum.no_confusion inl_eq_inr,
end

-- copypaste (III) begins
private lemma wrap_never_outputs_H {N : Type} {a : symbol T N} :
  wrap_sym a ≠ H :=
begin
  unfold H,
  cases a;
  unfold wrap_sym,
  {
    apply symbol.no_confusion,
  },
  intro contr,
  have inl_eq_inr := symbol.nonterminal.inj contr,
  exact sum.no_confusion inl_eq_inr,
end
-- copypaste (III) ends

-- copypaste (III) begins
private lemma wrap_never_outputs_R {N : Type} {a : symbol T N} :
  wrap_sym a ≠ R :=
begin
  unfold R,
  cases a;
  unfold wrap_sym,
  {
    apply symbol.no_confusion,
  },
  intro contr,
  have inl_eq_inr := symbol.nonterminal.inj contr,
  exact sum.no_confusion inl_eq_inr,
end
-- copypaste (III) ends

example {l : list (list ℕ)} {x y z : list ℕ}
    (l_nozeros : ∀ lᵢ ∈ l, 0 ∉ lᵢ) (y_nonzero : 0 ∉ y) (y_nonempty : 0 < y.length)
    (hyp : (list.map (++ [0]) l).join = x ++ y ++ z) :
  ∃ k : ℕ, ∃ x' z' : list ℕ, ∃ k_lt : k < l.length,
    (list.map (++ [0]) (list.take k l)).join ++ x' = x ∧
    l.nth_le k k_lt = x' ++ y ++ z' ∧
    z' ++ [0] ++ (list.map (++ [0]) (list.drop k.succ l)).join = z :=
begin
  have eq_x := congr_arg (list.take x.length) hyp,
  rw list.append_assoc at eq_x,
  rw list.take_left at eq_x,
  obtain ⟨k, e, klt, elt, take_xl⟩ := @list.take_join_of_lt _ (list.map (++ [0]) l) x.length (by {
    have lens := congr_arg list.length hyp,
    rw list.length_append_append at lens,
    rw lens,
    clear_except y_nonempty,
    linarith,
  }),
  rw take_xl at eq_x,
  have eq_z := congr_arg (list.drop (x.length + y.length)) hyp,
  rw ←list.length_append at eq_z,
  rw list.drop_left at eq_z,
  have z_nonempty : 0 < z.length,
  {
    -- `(list.map (++ [0]) l).join` ends with `0`
    -- hence `x ++ y ++ z` ends with `0` by `rw hyp`
    -- if `z` was empty (for contradition)
    -- we could not satisfy both `(y_nonzero : 0 ∉ y)` and `(y_nonempty : 0 < y.length)`
    by_contradiction contra,
    push_neg at contra,
    rw nat.le_zero_iff at contra,
    rw list.length_eq_zero at contra,
    rw contra at *,
    clear contra,
    rw list.append_nil at *,
    have hyp_rev := congr_arg list.reverse hyp,
    rw list.reverse_append at hyp_rev,
    rw list.reverse_join at hyp_rev,
    rw list.map_map at hyp_rev,
    change (list.map (λ (v : list ℕ), list.reverse (v ++ [0])) l).reverse.join = y.reverse ++ x.reverse at hyp_rev,
    have hyp_new : (list.map (λ (v : list ℕ), 0 :: v.reverse) l).reverse.join = y.reverse ++ x.reverse,
    {
      convert hyp_rev,
      finish, -- TODO use `list.reverse_append` instead
    },
    have hyp_head := congr_fun (congr_arg list.nth hyp_new) 0,
    clear hyp_rev hyp_new,
    have yr_nonempty : 0 < y.reverse.length,
    {
      rw list.length_reverse,
      exact y_nonempty,
    },
    rw list.nth_append yr_nonempty at hyp_head,
    rw ←list.map_reverse at hyp_head,
    rw ←list.reverse_reverse l at hyp,
    cases l.reverse with w l',
    {
      exfalso,
      have nil_eq_xy : list.nil = x ++ y,
      {
        convert hyp,
      },
      have len_eq := congr_arg list.length nil_eq_xy,
      clear_except y_nonempty len_eq,
      rw list.length_append at len_eq,
      rw list.length at len_eq,
      apply nat.lt_irrefl 0,
      calc
        0 < y.length            : y_nonempty
      ... ≤ x.length + y.length : le_add_self
      ... = 0                   : len_eq.symm,
    },
    rw list.map_cons at hyp_head,
    have starts_with_zero :
      ∀ a : list ℕ, ∀ b : list (list ℕ), ((0 :: a) :: b).join.nth 0 = some 0,
    {
      intros a b,
      refl,
    },
    rw starts_with_zero at hyp_head,
    have zero_in_y := list.nth_mem hyp_head.symm,
    rw list.mem_reverse at zero_in_y,
    exact y_nonzero zero_in_y,
  },
  obtain ⟨q, b, qlt, blt, drop_xyl⟩ := @list.drop_join_of_lt _ (list.map (++ [0]) l) (x ++ y).length (by {
    have lens := congr_arg list.length hyp,
    rw list.length_append_append at lens,
    rw list.length_append,
    rw lens,
    clear_except z_nonempty,
    linarith,
  }),
  rw drop_xyl at eq_z,

  have qltll : q < l.length,
  {
    rwa list.length_map at qlt,
  },
  have kltll : k < l.length,
  {
    rwa list.length_map at klt,
  },
  have key : q = k,
  {
    have segment_left := congr_arg (list.take x.length) hyp,
    rw list.append_assoc at segment_left,
    rw list.take_left at segment_left,
    rw take_xl at segment_left,
    have segment_right := congr_arg (list.drop (x ++ y).length) hyp,
    rw list.drop_left at segment_right,
    rw drop_xyl at segment_right,
    have count_zeros := congr_arg (λ l, list.count_in l 0) hyp,
    dsimp at count_zeros,

    have count_in_l : list.count_in (list.map (++ [0]) l).join 0 = l.length,
    {
      rw list.count_in_join,
      rw list.map_map,
      change (list.map (λ (w : list ℕ), list.count_in (w ++ [0]) 0) l).sum = l.length,
      simp [list.count_in_append, list.count_in],
      clear_except l_nozeros,
      change (list.map (λ (w : list ℕ), list.count_in w 0) l).sum = 0,
      have counted_zero : ∀ (w : list ℕ), w ∈ l → list.count_in w 0 = 0,
      {
        intros w winl,
        exact list.count_in_zero_of_notin (l_nozeros w winl),
      },
      induction l with x r ih,
      {
        refl,
      },
      rw list.map_cons,
      rw counted_zero x (list.mem_cons_self x r),
      rw list.sum_cons,
      rw nat.zero_add,
      apply ih;
      finish,
    },
    have count_in_k : list.count_in (list.take k (list.map (++ [0]) l)).join 0 = k,
    {
      -- similar to `list.count_in_l` TODO
      sorry,
    },
    have count_in_e : list.count_in (list.take e ((list.map (++ [0]) l).nth_le k klt)) 0 = 0,
    {
      apply list.count_in_zero_of_notin,
      rw list.nth_le_map,
      swap, {
        exact kltll,
      },
      rw list.take_append_of_le_length,
      swap, {
        rwa [list.nth_le_map', list.length_append, list.length_singleton, nat.lt_succ_iff ] at elt,
      },
      intro contr,
      exact l_nozeros (l.nth_le k kltll) (list.nth_le_mem l k kltll) (list.mem_of_mem_take contr),
    },
    have count_in_b : list.count_in (list.drop b ((list.map (++ [0]) l).nth_le q qlt)) 0 = 1,
    {
      -- kinda similar to `list.count_in_e` TODO
      sorry,
    },
    have count_in_q : list.count_in (list.drop q.succ (list.map (++ [0]) l)).join 0 = l.length - q.succ,
    {
      -- similar to `list.count_in_l` TODO
      sorry,
    },
    rw [count_in_l,
      list.count_in_append, list.count_in_append, list.count_in_zero_of_notin y_nonzero, add_zero,
      ←segment_left, ←segment_right, list.count_in_append, list.count_in_append,
      count_in_k, count_in_e, count_in_b, count_in_q, add_zero] at count_zeros,
    clear_except count_zeros qltll,
    omega,
  },
  use [k, list.take e ((list.map (++ [0]) l).nth_le k klt), list.drop b (l.nth_le q qltll)],
  use kltll,
  split,
  {
    convert eq_x,
    apply list.map_take,
  },
  split,
  swap, {
    rw key at *,
    convert eq_z,
    {
      rw list.nth_le_map',
      rw list.drop_append_of_le_length,
      rw list.nth_le_map at blt,
      swap, {
        assumption,
      },
      rw list.length_append at blt,
      rw list.length_singleton at blt,
      rwa nat.lt_succ_iff at blt,
    },
    {
      rw list.map_drop,
      rw key,
    },
  },
  rw ←list.take_append_drop x.length (list.map (++ [0]) l).join at hyp,
  rw take_xl at hyp,
  rw ←list.take_append_drop y.length (list.drop x.length (list.map (++ [0]) l).join) at hyp,
  rw list.drop_drop at hyp,
  rw add_comm at hyp,
  rw ←list.length_append at hyp,
  rw drop_xyl at hyp,
  have y_mid : y = list.take y.length (list.drop x.length (list.map (++ [0]) l).join),
  {
    rw [eq_x, eq_z] at hyp,
    clear_except hyp,
    rw list.append_assoc at hyp,
    have dxh := congr_arg (list.drop x.length) hyp,
    rw list.drop_left at dxh,
    rw list.drop_left at dxh,
    have rev := congr_arg list.reverse dxh,
    rw list.reverse_append at rev,
    rw list.reverse_append at rev,
    have dzr := congr_arg (list.drop z.reverse.length) rev,
    rw list.drop_left at dzr,
    rw list.drop_left at dzr,
    rw list.reverse_inj at dzr,
    exact dzr.symm,
  },
  rw y_mid,
  have subst_kq : l.nth_le q qltll = l.nth_le k kltll,
  {
    clear_except key,
    finish,
  },
  rw subst_kq,
  rw list.nth_le_map,
  swap, {
    exact kltll,
  },
  have tech : e ≤ b,
  {
    sorry,
  },
  have easy : list.take e (l.nth_le k kltll ++ [0]) = list.take e (l.nth_le k kltll),
  {
    clear_except elt,
    rw list.take_append_of_le_length,
    rw [list.nth_le_map', list.length_append, list.length_singleton] at elt,
    rwa nat.lt_succ_iff at elt,
  },
  rw easy,
  have hard :
    list.take y.length (list.drop x.length (list.map (++ [0]) l).join) =
    list.take (b - e) (list.drop e (l.nth_le k kltll)),
  {
    sorry,
  },
  rw hard,
  clear_except tech,
  rw ←list.drop_take,
  rw nat.add_sub_of_le tech,
  rw list.append_assoc,
  nth_rewrite 0 ←(list.take_append_drop e (l.nth_le k kltll)),
  congr,
  obtain ⟨d, hd⟩ := nat.le.dest tech,
  rw ←hd,
  rw list.drop_take,
  rw add_comm,
  rw ←list.drop_drop,
  rw list.take_append_drop,
end

private lemma case_1_match_rule {g : grammar T} {r₀ : grule T g.nt}
    {x : list (list (symbol T g.nt))} {u v : list (ns T g.nt)}
    (H_not_in_mid : H ∉
      list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ list.map wrap_sym r₀.input_R)
    (ass : Z :: (list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x))) =
      u ++ list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        list.map wrap_sym r₀.input_R ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : list (symbol T g.nt),
    u = Z :: list.join (list.map (++ [H]) (list.take m (list.map (list.map wrap_sym) x))) ++ list.map wrap_sym u₁
    ∧ list.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁) ∧
    v = list.map wrap_sym v₁ ++ [H] ++
        list.join (list.map (++ [H]) (list.drop m.succ (list.map (list.map wrap_sym) x))) :=
begin
  sorry,
end

private lemma star_case_1 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ x : list (list (symbol T g.nt)),
      (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
      (α = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) :
-- Do not change even though the statement could easily be made stronger!
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α' = list.map symbol.terminal u) ∨
  (∃ σ : list (symbol T g.nt), α' = list.map wrap_sym σ ++ [R]) ∨
  ((∃ ω : list (symbol T g.nt), α' = list.map wrap_sym ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α') :=
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
      exact R_neq_Z contr,
    },
    rw list.mem_join at contr,
    rw list.map_map at contr,
    rcases contr with ⟨l, lin, Ril⟩,
    rw list.mem_map at lin,
    rcases lin with ⟨y, -, eq_l⟩,
    change (list.map wrap_sym y ++ [H]) = l at eq_l,
    rw ←eq_l at Ril,
    rw list.mem_append at Ril,
    cases Ril,
    {
      rw list.mem_map at Ril,
      rcases Ril with ⟨s, -, imposs⟩,
      exact wrap_never_outputs_R imposs,
    },
    {
      rw list.mem_singleton at Ril,
      clear_except Ril,
      exact R_neq_H Ril,
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
    dsimp at *,
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
      have Z_not_in_tail : Z ∉ (list.map (++ [H]) (list.map (list.map wrap_sym) x)).join,
      -- TODO extract this prop?
      {
        intro Zin,
        clear_except Zin,
        rw list.map_map at Zin,
        rw list.mem_join at Zin,
        rcases Zin with ⟨l, lin, Zil⟩,
        rw list.mem_map at lin,
        rcases lin with ⟨z, -, eq_l⟩,
        change (list.map wrap_sym z ++ [H]) = l at eq_l,
        rw ←eq_l at Zil,
        rw list.mem_append at Zil,
        cases Zil,
        {
          rw list.mem_map at Zil,
          rcases Zil with ⟨s, -, imposs⟩,
          exact wrap_never_outputs_Z imposs,
        },
        {
          rw list.mem_singleton at Zil,
          clear_except Zil,
          exact Z_neq_H Zil,
        },
      },
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
        clear_except ul_pos,
        rw list.length at ul_pos,
        exact nat.lt_irrefl 0 ul_pos,
      },
      {
        dsimp at bef_tail,
        have Z_in_tail : Z ∈ l ++ [symbol.nonterminal (sum.inr 0)] ++ v,
        {
          apply list.mem_append_left,
          apply list.mem_append_right,
          apply list.mem_singleton_self,
        },
        rw bef_tail at Z_not_in_tail,
        exact Z_not_in_tail Z_in_tail,
      },
    },
    have v_rest : v = list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)),
    {
      rw u_nil at bef,
      clear_except bef,
      finish,
    },
    rw aft,
    rw [u_nil, v_rest],
    rw [list.nil_append, list.map_cons],
    refl,
  },
  cases rin,
  {
    right, left,
    rw rin at *,
    clear rin,
    dsimp at *,
    rw [list.append_nil, list.append_nil] at bef,
    use x,
    split,
    {
      exact valid,
    },
    -- copypaste (I) begins
    have u_nil : u = [],
    {
      clear_except bef,
      have Z_not_in_tail : Z ∉ (list.map (++ [H]) (list.map (list.map wrap_sym) x)).join,
      {
        intro Zin,
        clear_except Zin,
        rw list.map_map at Zin,
        rw list.mem_join at Zin,
        rcases Zin with ⟨l, lin, Zil⟩,
        rw list.mem_map at lin,
        rcases lin with ⟨z, -, eq_l⟩,
        change (list.map wrap_sym z ++ [H]) = l at eq_l,
        rw ←eq_l at Zil,
        rw list.mem_append at Zil,
        cases Zil,
        {
          rw list.mem_map at Zil,
          rcases Zil with ⟨s, -, imposs⟩,
          exact wrap_never_outputs_Z imposs,
        },
        {
          rw list.mem_singleton at Zil,
          clear_except Zil,
          exact Z_neq_H Zil,
        },
      },
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
        clear_except ul_pos,
        rw list.length at ul_pos,
        exact nat.lt_irrefl 0 ul_pos,
      },
      {
        dsimp at bef_tail,
        have Z_in_tail : Z ∈ l ++ [symbol.nonterminal (sum.inr 0)] ++ v,
        {
          apply list.mem_append_left,
          apply list.mem_append_right,
          apply list.mem_singleton_self,
        },
        rw bef_tail at Z_not_in_tail,
        exact Z_not_in_tail Z_in_tail,
      },
    },
    have v_rest : v = list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)),
    {
      rw u_nil at bef,
      clear_except bef,
      finish,
    },
    rw aft,
    rw [u_nil, v_rest],
    -- copypaste (I) ends
    refl,
  },
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
  -- copypaste (II) begins
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
  -- copypaste (II) ends
  have rin' : r ∈ rules_that_scan_terminals g ∨ r ∈ list.map wrap_gr g.rules,
  {
    rw or_comm,
    rwa ←list.mem_append,
  },
  clear rin,
  -- nearly copypaste (II) begins
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
  -- nearly copypaste (II) ends
  left,
  rw list.mem_map at rin',
  rcases rin' with ⟨r₀, orig_in, wrap_orig⟩,
  unfold wrap_gr at wrap_orig,
  rw ←wrap_orig at *,
  clear wrap_orig,
  dsimp at *,
  have H_not_in_middle :
    H ∉ list.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        list.map wrap_sym r₀.input_R,
  {
    intro contra,
    clear_except contra,
    rw list.mem_append at contra,
    cases contra,
    swap, {
      rw list.mem_map at contra,
      rcases contra with ⟨s, -, is_H⟩,
      exact wrap_never_outputs_H is_H,
    },
    rw list.mem_append at contra,
    cases contra,
    {
      -- copypaste (VI) begins
      rw list.mem_map at contra,
      rcases contra with ⟨s, -, is_H⟩,
      exact wrap_never_outputs_H is_H,
      -- copypaste (VI) ends
    },
    {
      rw list.mem_singleton at contra,
      have imposs := symbol.nonterminal.inj contra,
      exact sum.no_confusion imposs,
    },
  },
  rcases case_1_match_rule H_not_in_middle bef with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
  clear bef,
  rw [u_eq, v_eq] at aft,
  use (list.take m x ++ [u₁ ++ r₀.output_string ++ v₁] ++ list.drop m.succ x),
  split,
  {
    intros xᵢ xiin,
    rw list.mem_append at xiin,
    rw list.mem_append at xiin,
    cases xiin,
    swap, {
      apply valid,
      exact list.mem_of_mem_drop xiin,
    },
    cases xiin,
    {
      apply valid,
      exact list.mem_of_mem_take xiin,
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
      apply valid (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁),
      exact list.nth_mem xm_eq,
    },
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
  rw list.join_append,
  rw list.join_append,
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

private lemma star_case_2 {g : grammar T} {α α' : list (symbol T (star_grammar g).nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ x : list (list (symbol T g.nt)),
      (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
      (α = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) :
-- Do not change even though the statement could easily be made stronger!
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α' = list.map symbol.terminal u) ∨
  (∃ σ : list (symbol T g.nt), α' = list.map wrap_sym σ ++ [R]) ∨
  ((∃ ω : list (symbol T g.nt), α' = list.map wrap_sym ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α') :=
begin
  sorry,
end

private lemma star_case_3 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
      (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
      (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
      (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
      (α = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
        list.map wrap_sym γ ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) :
-- Do not change even though the statement could easily be made stronger!
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α' = list.map symbol.terminal u) ∨
  (∃ σ : list (symbol T g.nt), α' = list.map wrap_sym σ ++ [R]) ∨
  ((∃ ω : list (symbol T g.nt), α' = list.map wrap_sym ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α') :=
begin
  sorry,
end

private lemma star_case_4 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ u : list T, u ∈ (grammar_language g).star ∧ α = list.map symbol.terminal u) :
-- Do not change even though the statement could easily be made stronger!
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α' = list.map symbol.terminal u) ∨
  (∃ σ : list (symbol T g.nt), α' = list.map wrap_sym σ ++ [R]) ∨
  ((∃ ω : list (symbol T g.nt), α' = list.map wrap_sym ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α') :=
begin
  exfalso,
  rcases hyp with ⟨w, -, alpha_of_w⟩,
  rw alpha_of_w at orig,
  rcases orig with ⟨r, -, u, v, bef, -⟩,
  simpa using congr_arg (λ l, symbol.nonterminal r.input_N ∈ l) bef,
end

private lemma star_case_5 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ σ : list (symbol T g.nt), α = list.map wrap_sym σ ++ [R]) :
-- Do not change even though the statement could easily be made stronger!
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α' = list.map symbol.terminal u) ∨
  (∃ σ : list (symbol T g.nt), α' = list.map wrap_sym σ ++ [R]) ∨
  ((∃ ω : list (symbol T g.nt), α' = list.map wrap_sym ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α') :=
begin
  sorry,
end

private lemma false_of_wrap_concat_H_eq_appends {g : grammar T}
    {w : list (symbol T g.nt)} {v₁ v₂ v₄ v₅ : list (ns T g.nt)} {Y : ns T g.nt}
    (YneqH : Y ≠ H) (wrap_never_outs_Y : ∀ a : symbol T g.nt, wrap_sym a ≠ Y) :
  list.map wrap_sym w ++ [H] = v₁ ++ v₂ ++ [Y] ++ v₄ ++ v₅ → false :=
begin
  intro hyp,
  have contrast := congr_arg (λ l, Y ∈ l) hyp,
  have Y_not_in : (λ l, Y ∈ l) (list.map wrap_sym w ++ [H]) = false,
  {
    change (Y ∈ (list.map wrap_sym w ++ [H])) = false,
    rw [list.mem_append, list.mem_singleton, list.mem_map, eq_iff_iff, iff_false],
    by_contradiction if_Y_in,
    cases if_Y_in,
    {
      rcases if_Y_in with ⟨a, -, imposs⟩,
      exact wrap_never_outs_Y a imposs,
    },
    {
      exact YneqH if_Y_in,
    },
  },
  rw Y_not_in at contrast,
  simpa using contrast,
end

private lemma star_case_6 {g : grammar T} {α α' : list (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : (∃ ω : list (symbol T g.nt), α = list.map wrap_sym ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α) :
-- Do not change even though the statement could easily be made stronger!
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α' = list.map symbol.terminal u) ∨
  (∃ σ : list (symbol T g.nt), α' = list.map wrap_sym σ ++ [R]) ∨
  ((∃ ω : list (symbol T g.nt), α' = list.map wrap_sym ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α') :=
begin
  rcases hyp with ⟨⟨w, ends_with_H⟩, no_Z, no_R⟩,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,
  rw ends_with_H at bef,
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      exact false_of_wrap_concat_H_eq_appends Z_neq_H (@wrap_never_outputs_Z T g.nt) bef,
    },
  },
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      exact false_of_wrap_concat_H_eq_appends R_neq_H (@wrap_never_outputs_R T g.nt) bef,
    },
  },
  change r ∈ list.map wrap_gr g.rules ++ rules_that_scan_terminals g at rin,
  rw list.mem_append at rin,
  cases rin,
  {
    repeat {
      right,
    },
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
        -- copypaste (IX) begins
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
        -- copypaste (IX) ends
      },
    },
    use w.take u.length ++ r₀.output_string ++
      (w.drop (u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R).length).take (v.length - 1),
    rw aft,
    -- part "for later" begins
    have bef_len := congr_arg list.length bef,
    repeat {
      rw list.length_append at bef_len,
    },
    rw list.length_singleton at bef_len,
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
    -- part "for later" ends
    rw list.map_append_append,
    rw list.map_take,
    have bef_take := congr_arg (list.take u.length) bef,
    repeat {
      rw list.append_assoc at bef_take,
    },
    rw list.take_left at bef_take,
    rw list.take_append_of_le_length at bef_take,
    rw bef_take,
    trim,
    rw ←r_of_r₀,
    unfold wrap_gr,
    dsimp,
    have bef_drop := congr_arg (list.drop (u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R).length) bef,
    rw list.drop_left at bef_drop,
    rw list.drop_append_of_le_length at bef_drop,
    have bef_segm := congr_arg (list.take (v.length - 1)) bef_drop,
    rw list.take_append_of_le_length at bef_segm,
    rw ←r_of_r₀ at bef_segm,
    unfold wrap_gr at bef_segm,
    rw list.map_take,
    rw list.map_drop,
    rw bef_segm,
    rw list.append_assoc,
    apply congr_arg2,
    {
      refl,
    },
    clear_except bef vlnn,
    convert_to
      list.take (v.length - 1) v ++ list.drop (v.length - 1) v =
      list.take (v.length - 1) v ++ [H],
    {
      rw list.take_append_drop,
    },
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
    rw bef_rev_tak,
    -- and now close the residues from `_le_length` lemmata
    {
      clear_except bef_len vlnn,
      rw list.length_drop,
      repeat {
        rw list.length_append,
      },
      rw list.length_singleton at *,
      apply le_of_eq,
      obtain ⟨m, vlm⟩ := le_iff_exists_add.mp vlnn,
      rw vlm at *,
      clear vlm vlnn v,
      rw [add_comm, nat.add_succ_sub_one, add_zero],
      have almost : (list.map wrap_sym w).length = u.length + r.input_L.length + r.input_R.length + (1 + m),
      {
        linarith, -- TODO try to refactor to not need both `linarith` and `omega`
      },
      clear_except almost,
      omega,
    },
    iterate 2 {
      clear_except bef_len vlnn,
      repeat {
        rw list.length_append,
      },
      linarith,
    },
  },
  {
    exfalso,
    unfold rules_that_scan_terminals at rin,
    rw list.mem_map at rin,
    rcases rin with ⟨t, -, eq_r⟩,
    rw ←eq_r at bef,
    exact false_of_wrap_concat_H_eq_appends R_neq_H (@wrap_never_outputs_R T g.nt) bef,
  },
end

private lemma star_induction {g : grammar T} {α : list (ns T g.nt)}
    (ass : grammar_derives (star_grammar g) [Z] α) :
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = list.map symbol.terminal (list.join w) ++ list.map symbol.terminal β ++ [R] ++
      list.map wrap_sym γ ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α = list.map symbol.terminal u) ∨
  (∃ σ : list (symbol T g.nt), α = list.map wrap_sym σ ++ [R]) ∨
  ((∃ ω : list (symbol T g.nt), α = list.map wrap_sym ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α) :=
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
    exact star_case_1 orig ih,
  },
  cases ih,
  {
    exact star_case_2 orig ih,
  },
  cases ih,
  {
    exact star_case_3 orig ih,
  },
  cases ih,
  {
    exact star_case_4 orig ih,
  },
  cases ih,
  {
    exact star_case_5 orig ih,
  },
  {
    exact star_case_6 orig ih,
  },
end

end hard_direction


section easy_direction

private lemma short_induction {g : grammar T} {w : list (list T)}
    (ass : ∀ wᵢ ∈ w.reverse, grammar_generates g wᵢ) :
  grammar_derives (star_grammar g) [Z] (Z ::
      list.join (list.map (++ [H]) (list.map (list.map symbol.terminal) w.reverse))
    ) ∧
  ∀ p ∈ w, ∀ t ∈ p, symbol.terminal t ∈ list.join (list.map grule.output_string g.rules) :=
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
      have wrap_eq_lift : @wrap_sym T g.nt = lift_symbol_ sum.inl,
      {
        ext,
        cases x;
        refl,
      },
      let lifted_g : lifted_grammar_ T :=
        lifted_grammar_.mk g (star_grammar g) sum.inl sum.get_left (by {
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
            -- copypaste (VII) begins
            {
              simp only [sum.get_left] at hyp,
              exfalso,
              exact hyp,
            },
            -- copypaste (VII) ends
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
          unfold lift_rule_,
          unfold lift_string_,
          rw wrap_eq_lift,
        }) (by {
          rintros r ⟨rin, n, nrn⟩,
          cases rin,
          {
            exfalso,
            rw rin at nrn,
            exact sum.no_confusion nrn,
          },
          -- copypaste (VIII) begins
          cases rin,
          {
            exfalso,
            rw rin at nrn,
            exact sum.no_confusion nrn,
          },
          -- copypaste (VIII) ends and begins
          cases rin,
          {
            exfalso,
            rw rin at nrn,
            exact sum.no_confusion nrn,
          },
          -- copypaste (VIII) ends and begins
          cases rin,
          {
            exfalso,
            rw rin at nrn,
            exact sum.no_confusion nrn,
          },
          -- copypaste (VIII) ends
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
            unfold lift_rule_,
            unfold wrap_gr,
            unfold lift_string_,
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
          (lift_string_ lifted_g.lift_nt (list.map symbol.terminal v)),
      {
        unfold lift_string_,
        rw list.map_map,
        congr,
      },
      exact lift_deri_ lifted_g ass,
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

private lemma inductive_terminal_scan {g : grammar T} {w : list (list T)} (n : ℕ) (n_lt_wl : n ≤ w.length)
    (terminals : ∀ v ∈ w, ∀ t ∈ v, symbol.terminal t ∈ list.join (list.map grule.output_string g.rules)) :
  grammar_derives (star_grammar g)
    ((list.map (λ u, list.map symbol.terminal u) (list.take (w.length - n) w)).join ++ [R] ++
      (list.map (λ v, [H] ++ list.map symbol.terminal v) (list.drop (w.length - n) w)).join ++ [H])
    (list.map symbol.terminal w.join ++ [R, H]) :=
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
    (list.map symbol.terminal w.join ++ [R, H]) :=
begin
  rw list.map_map,
  convert inductive_terminal_scan w.length (by refl) terminals,
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


/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : language T) :
  is_RE L  →  is_RE L.star  :=
begin
  rintro ⟨g, hg⟩,
  use star_grammar g,

  apply set.eq_of_subset_of_subset,
  {
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
    -- copypaste (IV) begins
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
    -- copypaste (IV) ends
    cases result,
    {
      exfalso,
      rcases result with ⟨α, β, γ, x, -, -, -, contr⟩,
      have output_contains_R : R ∈ list.map symbol.terminal w,
      {
        rw contr,
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
      -- copypaste (V) begins
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
      -- copypaste (V) ends
    },
  },
  {
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
    clear_except terminated,
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
