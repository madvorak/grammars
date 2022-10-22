import unrestricted.grammar


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


private lemma wrap_never_outputs_Z {N : Type} (a : symbol T N) :
  wrap_sym a ≠ Z :=
begin
  unfold Z,
  cases a;
  unfold wrap_sym,
  {
    tauto,
  },
  intro contr,
  have inl_eq_inr := symbol.nonterminal.inj contr,
  clear_except inl_eq_inr,
  tauto,
end

-- copypaste (III) begins
private lemma wrap_never_outputs_H {N : Type} (a : symbol T N) :
  wrap_sym a ≠ H :=
begin
  unfold H,
  cases a;
  unfold wrap_sym,
  {
    tauto,
  },
  intro contr,
  have inl_eq_inr := symbol.nonterminal.inj contr,
  clear_except inl_eq_inr,
  tauto,
end
-- copypaste (III) ends

-- copypaste (III) begins
private lemma wrap_never_outputs_R {N : Type} (a : symbol T N) :
  wrap_sym a ≠ R :=
begin
  unfold R,
  cases a;
  unfold wrap_sym,
  {
    tauto,
  },
  intro contr,
  have inl_eq_inr := symbol.nonterminal.inj contr,
  clear_except inl_eq_inr,
  tauto,
end
-- copypaste (III) ends

example {l : list (list ℕ)} {x y z : list ℕ}
    (l_nozeros : ∀ lᵢ ∈ l, 0 ∉ lᵢ) (y_nonzero : 0 ∉ y)
    (hyp : (list.map (++ [0]) l).join = x ++ y ++ z) :
  ∃ k : ℕ, ∃ x' z' : list ℕ, ∃ k_le : k < l.length,
    (list.map (++ [0]) (list.take k l)).join ++ x' = x ∧
    l.nth_le k k_le = x' ++ y ++ z' ∧
    z' ++ [0] ++ (list.map (++ [0]) (list.drop k.succ l)).join = z :=
begin
  sorry,
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
    (α = (list.map symbol.terminal (list.join w)) ++ [R, H] ++
      list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α = list.map symbol.terminal u) ∨
  (∃ σ : list (symbol T g.nt), α = list.map wrap_sym σ ++ [R]) ∨
  (∃ ω : list (symbol T g.nt), α = list.map wrap_sym ω ++ [H] ∧ Z ∉ α ∧ R ∉ α) :=
begin
  induction ass with a b trash orig ih,
  {
    left,
    use list.nil,
    tauto,
  },
  cases ih,
  {
    rcases ih with ⟨x, valid, cat⟩,
    have no_R_in_a : R ∉ a,
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
        exact wrap_never_outputs_R s imposs,
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
            exact wrap_never_outputs_Z s imposs,
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
          exact nat.lt_asymm ul_pos ul_pos,
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
            exact wrap_never_outputs_Z s imposs,
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
          exact nat.lt_asymm ul_pos ul_pos,
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
      apply no_R_in_a,
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
      apply no_R_in_a,
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
      apply no_R_in_a,
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
        exact wrap_never_outputs_H s is_H,
      },
      rw list.mem_append at contra,
      cases contra,
      {
        -- copypaste (VI) begins
        rw list.mem_map at contra,
        rcases contra with ⟨s, -, is_H⟩,
        exact wrap_never_outputs_H s is_H,
        -- copypaste (VI) ends
      },
      {
        rw list.mem_singleton at contra,
        have imposs := symbol.nonterminal.inj contra,
        clear_except imposs,
        tauto,
      },
    },
    have befo : ∃ m : ℕ, ∃ u₁ v₁ : list (symbol T g.nt),
      u = Z :: list.join (list.map (++ [H]) (list.take m (list.map (list.map wrap_sym) x))) ++ list.map wrap_sym u₁
      ∧ list.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁) ∧
      v = list.map wrap_sym v₁ ++ [H] ++
          list.join (list.map (++ [H]) (list.drop m.succ (list.map (list.map wrap_sym) x))),
    {
      clear_except /-no_R_in_a-/ H_not_in_middle bef,
      -- number of `H`s in `u` plus in `v` is all of `x.length` follows from `H_not_in_middle` and `bef`
      -- hence `u` is a prefix that contains some quantity `m` of them
      -- and `v` is a suffix that contains `x.length - m` of them
      sorry,
    },
    clear bef,
    rcases befo with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
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
      refl,
    },
    repeat {
      rw ←list.append_assoc,
    },
    apply congr_arg2,
    swap, {
      rw ←list.map_drop,
      refl,
    },
    rw [
      list.map_singleton, list.map_singleton,
      list.join, list.join, list.append_nil,
      list.map_append, list.map_append
    ],
  },
  sorry,
end

private lemma short_induction {g : grammar T} {w : list (list T)}
    (ass : ∀ wᵢ ∈ w, grammar_generates g wᵢ) :
  grammar_derives (star_grammar g) [Z] (Z ::
      list.join (list.map (++ [H]) (list.map (list.map symbol.terminal) w))
    ) :=
begin
  induction w with v x ih,
  {
    apply grammar_deri_self,
  },
  specialize ih (by finish), -- TODO replace
  specialize ass v (list.mem_cons_self v x),
  unfold grammar_generates at ass,
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
  rw [list.nil_append, list.append_nil],
  rw [list.map_cons, list.map_cons, list.join],
  sorry,
end


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
      clear_except terminal_eq_Z,
      tauto,
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
      clear_except terminal_eq_R,
      tauto,
    },
    -- copypaste (IV) ends
    cases result,
    {
      exfalso,
      rcases result with ⟨y, -, -, x, -, -, -, contr⟩,
      have output_contains_R : R ∈ list.map symbol.terminal w,
      {
        rw contr,
        apply list.mem_append_left,
        apply list.mem_append_right,
        apply list.mem_cons_self,
      },
      rw list.mem_map at output_contains_R,
      rcases output_contains_R with ⟨t, -, terminal_eq_R⟩,
      clear_except terminal_eq_R,
      tauto,
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
        clear_except last_symbols, -- `none = some R`
        tauto,
      },
      {
        rw option.map_some' at last_symbols,
        have terminal_eq_R := option.some.inj last_symbols,
        clear_except terminal_eq_R,
        tauto,
      },
    },
    {
      exfalso,
      rcases result with ⟨ω, contr, -⟩,
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
        clear_except last_symbols, -- `none = some H`
        tauto,
      },
      {
        rw option.map_some' at last_symbols,
        have terminal_eq_H := option.some.inj last_symbols,
        clear_except terminal_eq_H,
        tauto,
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
    rw w_join,
    clear w_join p,
    unfold grammar_generates,
    rw ←hg at parts_in_L,
    apply grammar_deri_of_deri_deri (short_induction parts_in_L),
    apply grammar_deri_of_tran_deri,
    {
      use (star_grammar g).rules.nth_le 1 (by dec_trivial),
      split,
      {
        apply list.nth_le_mem,
      },
      use [[], (list.map (++ [H]) (list.map (list.map symbol.terminal) w)).join],
      split,
      {
        refl, -- performs several definitional equalities to verify the equality
      },
      {
        refl, -- binds the implicit argument of `grammar_deri_of_tran_deri` nothing to verify
      },
    },
    rw list.nil_append,
    sorry,
  },
end
