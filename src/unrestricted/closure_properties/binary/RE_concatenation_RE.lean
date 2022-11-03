import unrestricted.grammar


section list_technicalities
variables {α β : Type}

lemma list_forall₂_nth_le {R : α → β → Prop} :
  ∀ {x : list α}, ∀ {y : list β}, list.forall₂ R x y →
    ∀ {i : ℕ}, ∀ i_lt_len_x : i < x.length, ∀ i_lt_len_y : i < y.length,
      R (x.nth_le i i_lt_len_x) (y.nth_le i i_lt_len_y)
| []       []       := by { intros hyp i hx, exfalso, apply nat.not_lt_zero, exact hx, }
| []       (a₂::l₂) := by { intro hyp, exfalso, cases hyp, }
| (a₁::l₁) []       := by { intro hyp, exfalso, cases hyp, }
| (a₁::l₁) (a₂::l₂) :=
begin
  intros ass i i_lt_len_x i_lt_len_y,
  rw list.forall₂_cons at ass,
  cases i,
  {
    unfold list.nth_le,
    exact ass.1,
  },
  unfold list.nth_le,
  apply list_forall₂_nth_le,
  exact ass.2,
end

lemma list_filter_map_eq_of_map_eq_map_some {f : α → option β} :
  ∀ {x : list α}, ∀ {y : list β},
    list.map f x = list.map option.some y →
      list.filter_map f x = y
| []       []       := λ _, rfl
| []       (a₂::l₂) := by { intro hyp, exfalso, apply list.cons_ne_nil, exact hyp.symm, }
| (a₁::l₁) []       := by { intro hyp, exfalso, apply list.cons_ne_nil, exact hyp, }
| (a₁::l₁) (a₂::l₂) :=
begin
  intro ass,
  rw list.map at ass,
  rw list.map at ass,
  rw list.cons.inj_eq at ass,
  rw list.filter_map_cons_some _ _ _ ass.1,
  congr,
  apply list_filter_map_eq_of_map_eq_map_some,
  exact ass.2,
end

end list_technicalities


-- new nonterminal type
protected def nnn (T N₁ N₂ : Type) : Type :=
option (N₁ ⊕ N₂) ⊕ (T ⊕ T)

-- new symbol type
private def nst (T N₁ N₂ : Type) : Type :=
symbol T (nnn T N₁ N₂)

variables {T : Type}


section the_construction

protected def wrap_symbol₁ {N₁ : Type} (N₂ : Type) : symbol T N₁ → nst T N₁ N₂
| (symbol.terminal t)    := symbol.nonterminal (sum.inr (sum.inl t))
| (symbol.nonterminal n) := symbol.nonterminal (sum.inl (some (sum.inl n)))

protected def wrap_symbol₂ {N₂ : Type} (N₁ : Type) : symbol T N₂ → nst T N₁ N₂
| (symbol.terminal t)    := symbol.nonterminal (sum.inr (sum.inr t))
| (symbol.nonterminal n) := symbol.nonterminal (sum.inl (some (sum.inr n)))

private def wrap_grule₁ {N₁ : Type} (N₂ : Type) (r : grule T N₁) : grule T (nnn T N₁ N₂) :=
grule.mk
  (list.map (wrap_symbol₁ N₂) r.input_L)
  (sum.inl (some (sum.inl r.input_N)))
  (list.map (wrap_symbol₁ N₂) r.input_R)
  (list.map (wrap_symbol₁ N₂) r.output_string)

private def wrap_grule₂ {N₂ : Type} (N₁ : Type) (r : grule T N₂) : grule T (nnn T N₁ N₂) :=
grule.mk
  (list.map (wrap_symbol₂ N₁) r.input_L)
  (sum.inl (some (sum.inr r.input_N)))
  (list.map (wrap_symbol₂ N₁) r.input_R)
  (list.map (wrap_symbol₂ N₁) r.output_string)

protected def rules_for_terminals₁ (N₂ : Type) (g : grammar T) : list (grule T (nnn T g.nt N₂)) :=
list.map (λ t, grule.mk [] (sum.inr (sum.inl t)) [] [symbol.terminal t]) (all_used_terminals g)

protected def rules_for_terminals₂ (N₁ : Type) (g : grammar T) : list (grule T (nnn T N₁ g.nt)) :=
list.map (λ t, grule.mk [] (sum.inr (sum.inr t)) [] [symbol.terminal t]) (all_used_terminals g)

-- the grammar for concatenation of `g₁` and `g₂` languages
protected def big_grammar (g₁ g₂ : grammar T) : grammar T :=
grammar.mk (nnn T g₁.nt g₂.nt) (sum.inl none) (
  (grule.mk [] (sum.inl none) [] [
    symbol.nonterminal (sum.inl (some (sum.inl g₁.initial))),
    symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]
  ) :: (
    (list.map (wrap_grule₁ g₂.nt) g₁.rules ++ list.map (wrap_grule₂ g₁.nt) g₂.rules) ++
    (rules_for_terminals₁ g₂.nt g₁ ++ rules_for_terminals₂ g₁.nt g₂)
  )
)

end the_construction


section easy_direction

private lemma first_transformation {g₁ g₂ : grammar T} :
  grammar_transforms (big_grammar g₁ g₂) [symbol.nonterminal (big_grammar g₁ g₂).initial] [
      symbol.nonterminal (sum.inl (some (sum.inl g₁.initial))),
      symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))
    ] :=
begin
  use (big_grammar g₁ g₂).rules.nth_le 0 dec_trivial,
  split,
  {
    change _ ∈ list.cons _ _,
    finish,
  },
  use [[], []],
  split;
  refl,
end

private lemma grammar_generates_only_legit_terminals
    {g : grammar T}
    {w : list (symbol T g.nt)}
    (ass : grammar_derives g [symbol.nonterminal g.initial] w)
    {s : symbol T g.nt}
    (symbol_derived : s ∈ w) :
  (∃ r : grule T g.nt, r ∈ g.rules ∧ s ∈ r.output_string) ∨
  (s = symbol.nonterminal g.initial) :=
begin
  induction ass with x y trash orig ih,
  {
    rw list.mem_singleton at symbol_derived,
    right,
    exact symbol_derived,
  },
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,
  rw aft at symbol_derived,
  rw list.mem_append at symbol_derived,
  rw list.mem_append at symbol_derived,
  cases symbol_derived,
  cases symbol_derived,
  {
    apply ih,
    rw bef,
    repeat {
      rw list.mem_append,
      left,
    },
    exact symbol_derived,
  },
  {
    left,
    use r,
    split,
    {
      exact rin,
    },
    {
      exact symbol_derived,
    },
  },
  {
    apply ih,
    rw bef,
    rw list.mem_append,
    right,
    exact symbol_derived,
  },
end

private lemma substitute_terminals
    {g₁ g₂ : grammar T}
    {side : T → T ⊕ T}
    {w : list T}
    (rule_for_each_terminal : ∀ t ∈ w,
      (grule.mk [] (sum.inr (side t)) [] [symbol.terminal t]) ∈
        (rules_for_terminals₁ g₂.nt g₁ ++ rules_for_terminals₂ g₁.nt g₂)) :
  grammar_derives (big_grammar g₁ g₂)
    (list.map (symbol.nonterminal ∘ sum.inr ∘ side) w)
    (list.map symbol.terminal w) :=
begin
  induction w with d l ih,
  {
    apply grammar_deri_self,
  },
  rw list.map,
  rw list.map,
  rw ←list.singleton_append,
  rw ←list.singleton_append,
  have step_head :
    grammar_transforms (big_grammar g₁ g₂)
      ([(symbol.nonterminal ∘ sum.inr ∘ side) d] ++ list.map (symbol.nonterminal ∘ sum.inr ∘ side) l)
      ([symbol.terminal d] ++ list.map (symbol.nonterminal ∘ sum.inr ∘ side) l),
  {
    use grule.mk [] (sum.inr (side d)) [] [symbol.terminal d],
    split,
    {
      change _ ∈ list.cons _ _,
      apply list.mem_cons_of_mem,
      apply list.mem_append_right,
      apply rule_for_each_terminal,
      apply list.mem_cons_self,
    },
    use [[], list.map (symbol.nonterminal ∘ sum.inr ∘ side) l],
    split;
    refl,
  },
  apply grammar_deri_of_tran_deri step_head,
  apply grammar_deri_with_prefix,
  apply ih,
  {
    intros t tin,
    apply rule_for_each_terminal t,
    exact list.mem_cons_of_mem d tin,
  },
end

protected lemma in_big_of_in_concatenated
    {g₁ g₂ : grammar T}
    {w : list T}
    (ass : w ∈ grammar_language g₁ * grammar_language g₂) :
  w ∈ grammar_language (big_grammar g₁ g₂) :=
begin
  rw language.mem_mul at ass,
  rcases ass with ⟨u, v, hu, hv, hw⟩,
  unfold grammar_language at *,
  rw set.mem_set_of_eq at *,
  unfold grammar_generates at *,
  apply grammar_deri_of_tran_deri first_transformation,

  rw ←hw,
  rw list.map_append,

  apply @grammar_deri_of_deri_deri T (big_grammar g₁ g₂) _
    (list.map symbol.terminal u ++ [symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]) _,
  {
    clear_except hu,
    rw ←list.singleton_append,
    apply grammar_deri_with_postfix,
    apply @grammar_deri_of_deri_deri _ _ _ (list.map (
        (@symbol.nonterminal T (big_grammar g₁ g₂).nt) ∘ sum.inr ∘ sum.inl
      ) u) _,
    {
      have upgrade_deri₁ :
        ∀ w : list (symbol T g₁.nt),
          grammar_derives g₁ [symbol.nonterminal g₁.initial] w →
            grammar_derives (big_grammar g₁ g₂)
              [symbol.nonterminal (sum.inl (some (sum.inl g₁.initial)))]
              (list.map (wrap_symbol₁ g₂.nt) w),
      {
        clear_except,
        intros w deri₁,
        induction deri₁ with x y trash orig ih,
        {
          apply grammar_deri_self,
        },
        apply grammar_deri_of_deri_tran ih,
        clear_except orig,
        rcases orig with ⟨r, rin, u, v, bef, aft⟩,
        use wrap_grule₁ g₂.nt r,
        split,
        {
          change wrap_grule₁ g₂.nt r ∈ (_ :: ((
              (list.map (wrap_grule₁ g₂.nt) g₁.rules) ++
              (list.map (wrap_grule₂ g₁.nt) g₂.rules)
            ) ++ _)),
          apply list.mem_cons_of_mem,
          apply list.mem_append_left,
          apply list.mem_append_left,
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
        use list.map (wrap_symbol₁ g₂.nt) u,
        use list.map (wrap_symbol₁ g₂.nt) v,
        split,
        {
          convert congr_arg (list.map (wrap_symbol₁ g₂.nt)) bef,
          rw list.map_append_append,
          rw list.map_append_append,
          refl,
        },
        {
          convert congr_arg (list.map (wrap_symbol₁ g₂.nt)) aft,
          rw list.map_append_append,
          refl,
        },
      },
      have upgraded := upgrade_deri₁ _ hu,
      rw list.map_map at upgraded,
      exact upgraded,
    },
    {
      have legit_terminals₁ :
        ∀ t ∈ u, ∃ r : grule T g₁.nt,
          r ∈ g₁.rules ∧ symbol.terminal t ∈ r.output_string,
      {
        intros t tin,
        have tin' : symbol.terminal t ∈ list.map symbol.terminal u,
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
        have legit := grammar_generates_only_legit_terminals hu tin',
        cases legit,
        {
          exact legit,
        },
        {
          exfalso,
          clear_except legit,
          tauto,
        },
      },
      apply substitute_terminals,
      {
        intros t tin,
        apply list.mem_append_left,
        unfold rules_for_terminals₁,
        rw list.mem_map,
        use t,
        split,
        {
          unfold all_used_terminals,
          rw list.mem_filter_map,
          use symbol.terminal t,
          split,
          {
            rw list.mem_join,
            obtain ⟨r, rin, sttin⟩ := legit_terminals₁ t tin,
            use r.output_string,
            split,
            {
              apply list.mem_map_of_mem,
              exact rin,
            },
            {
              exact sttin,
            },
          },
          {
            refl,
          },
        },
        {
          refl,
        },
      },
    },
  },
  {
    clear_except hv,
    apply grammar_deri_with_prefix,
    apply @grammar_deri_of_deri_deri _ _ _ (list.map (
        (@symbol.nonterminal T (big_grammar g₁ g₂).nt) ∘ sum.inr ∘ sum.inr
      ) v) _,
    {
      have upgrade_deri₂ :
        ∀ w : list (symbol T g₂.nt),
          grammar_derives g₂ [symbol.nonterminal g₂.initial] w →
            grammar_derives (big_grammar g₁ g₂)
              [symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]
              (list.map (wrap_symbol₂ g₁.nt) w),
      {
        clear_except,
        intros w deri₁,
        induction deri₁ with x y trash orig ih,
        {
          apply grammar_deri_self,
        },
        apply grammar_deri_of_deri_tran ih,
        clear_except orig,
        rcases orig with ⟨r, rin, u, v, bef, aft⟩,
        use wrap_grule₂ g₁.nt r,
        split,
        {
          change wrap_grule₂ g₁.nt r ∈ (_ :: ((
              (list.map (wrap_grule₁ g₂.nt) g₁.rules) ++
              (list.map (wrap_grule₂ g₁.nt) g₂.rules)
            ) ++ _)),
          apply list.mem_cons_of_mem,
          apply list.mem_append_left,
          apply list.mem_append_right,
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
        use list.map (wrap_symbol₂ g₁.nt) u,
        use list.map (wrap_symbol₂ g₁.nt) v,
        split,
        {
          convert congr_arg (list.map (wrap_symbol₂ g₁.nt)) bef,
          rw list.map_append_append,
          rw list.map_append_append,
          refl,
        },
        {
          convert congr_arg (list.map (wrap_symbol₂ g₁.nt)) aft,
          rw list.map_append_append,
          refl,
        },
      },
      have upgraded := upgrade_deri₂ _ hv,
      rw list.map_map at upgraded,
      exact upgraded,
    },
    {
      have legit_terminals₂ :
        ∀ t ∈ v, ∃ r : grule T g₂.nt,
          r ∈ g₂.rules ∧ symbol.terminal t ∈ r.output_string,
      {
        intros t tin,
        have tin' : symbol.terminal t ∈ list.map symbol.terminal v,
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
        have legit := grammar_generates_only_legit_terminals hv tin',
        cases legit,
        {
          exact legit,
        },
        {
          exfalso,
          clear_except legit,
          tauto,
        },
      },
      apply substitute_terminals,
      {
        intros t tin,
        apply list.mem_append_right,
        unfold rules_for_terminals₂,
        rw list.mem_map,
        use t,
        split,
        {
          unfold all_used_terminals,
          rw list.mem_filter_map,
          use symbol.terminal t,
          split,
          {
            rw list.mem_join,
            obtain ⟨r, rin, sttin⟩ := legit_terminals₂ t tin,
            use r.output_string,
            split,
            {
              apply list.mem_map_of_mem,
              exact rin,
            },
            {
              exact sttin,
            },
          },
          {
            refl,
          },
        },
        {
          refl,
        },
      },
    },
  },
end

end easy_direction


section hard_direction

section correspondence_for_terminals

private def corresponding_symbols {N₁ N₂ : Type} : nst T N₁ N₂ → nst T N₁ N₂ → Prop
| (symbol.terminal t)                               (symbol.terminal t')                               := t = t'
| (symbol.nonterminal (sum.inr (sum.inl a)))        (symbol.nonterminal (sum.inr (sum.inl a')))        := a = a'
| (symbol.nonterminal (sum.inr (sum.inr a)))        (symbol.nonterminal (sum.inr (sum.inr a')))        := a = a'
| (symbol.nonterminal (sum.inr (sum.inl a)))        (symbol.terminal t)                                := t = a
| (symbol.nonterminal (sum.inr (sum.inr a)))        (symbol.terminal t)                                := t = a
| (symbol.nonterminal (sum.inl (some (sum.inl n)))) (symbol.nonterminal (sum.inl (some (sum.inl n')))) := n = n'
| (symbol.nonterminal (sum.inl (some (sum.inr n)))) (symbol.nonterminal (sum.inl (some (sum.inr n')))) := n = n'
| (symbol.nonterminal (sum.inl (none)))             (symbol.nonterminal (sum.inl (none)))              := true
| _                                                 _                                                  := false

private lemma corresponding_symbols_self {N₁ N₂ : Type} (s : nst T N₁ N₂) : corresponding_symbols s s :=
begin
  repeat {
    try {
      cases s,
    },
    try {
      unfold corresponding_symbols,
    },
  },
end

private lemma corresponding_symbols_never₁ {N₁ N₂ : Type} {s₁ : symbol T N₁} {s₂ : symbol T N₂} :
  ¬ corresponding_symbols (wrap_symbol₁ N₂ s₁) (wrap_symbol₂ N₁ s₂) :=
begin
  cases s₁;
  cases s₂;
  {
    unfold wrap_symbol₁,
    unfold wrap_symbol₂,
    unfold corresponding_symbols,
    exact not_false,
  },
end

private lemma corresponding_symbols_never₂ {N₁ N₂ : Type} {s₁ : symbol T N₁} {s₂ : symbol T N₂} :
  ¬ corresponding_symbols (wrap_symbol₂ N₁ s₂) (wrap_symbol₁ N₂ s₁) :=
begin
  cases s₁;
  cases s₂;
  {
    unfold wrap_symbol₁,
    unfold wrap_symbol₂,
    unfold corresponding_symbols,
    exact not_false,
  },
end


private def corresponding_strings {N₁ N₂ : Type} : list (nst T N₁ N₂) → list (nst T N₁ N₂) → Prop :=
list.forall₂ corresponding_symbols

private lemma corresponding_strings_self {N₁ N₂ : Type} {x : list (nst T N₁ N₂)} :
  corresponding_strings x x :=
begin
  apply list.forall₂_same,
  intros s trash,
  exact corresponding_symbols_self s,
end

private lemma corresponding_strings_singleton {N₁ N₂ : Type} {s₁ s₂ : nst T N₁ N₂}
    (ass : corresponding_symbols s₁ s₂) :
  corresponding_strings [s₁] [s₂] :=
begin
  unfold corresponding_strings,
  rw list.forall₂_cons,
  split,
  {
    exact ass,
  },
  {
    exact list.forall₂.nil,
  },
end

private lemma corresponding_strings_append {N₁ N₂ : Type} {x₁ x₂ y₁ y₂ : list (nst T N₁ N₂)}
    (ass₁ : corresponding_strings x₁ y₁)
    (ass₂ : corresponding_strings x₂ y₂) :
  corresponding_strings (x₁ ++ x₂) (y₁ ++ y₂) :=
begin
  unfold corresponding_strings at *,
  exact list.rel_append ass₁ ass₂,
end

private lemma corresponding_strings_length {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (ass : corresponding_strings x y) :
  x.length = y.length :=
begin
  unfold corresponding_strings at ass,
  exact list.forall₂_length_eq ass,
end

private lemma corresponding_strings_nth_le {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)} {i : ℕ}
    (i_lt_len_x : i < x.length) (i_lt_len_y : i < y.length)
    (ass : corresponding_strings x y) :
  corresponding_symbols (x.nth_le i i_lt_len_x) (y.nth_le i i_lt_len_y) :=
begin
  apply list_forall₂_nth_le,
  exact ass,
end

private lemma corresponding_strings_reverse {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (ass : corresponding_strings x y) :
  corresponding_strings x.reverse y.reverse :=
begin
  unfold corresponding_strings at *,
  rw list.forall₂_reverse_iff,
  exact ass,
end

private lemma corresponding_strings_of_reverse {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (ass : corresponding_strings x.reverse y.reverse) :
  corresponding_strings x y :=
begin
  unfold corresponding_strings at *,
  rw list.forall₂_reverse_iff at ass,
  exact ass,
end

private lemma corresponding_strings_take {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (n : ℕ) (ass : corresponding_strings x y) :
  corresponding_strings (list.take n x) (list.take n y) :=
begin
  unfold corresponding_strings at *,
  exact list.forall₂_take n ass,
end

private lemma corresponding_strings_drop {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (n : ℕ) (ass : corresponding_strings x y) :
  corresponding_strings (list.drop n x) (list.drop n y) :=
begin
  unfold corresponding_strings at *,
  exact list.forall₂_drop n ass,
end

private lemma corresponding_strings_split {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (n : ℕ) (ass : corresponding_strings x y) :
  corresponding_strings (list.take n x) (list.take n y) ∧
  corresponding_strings (list.drop n x) (list.drop n y) :=
begin
  split,
  {
    exact corresponding_strings_take n ass,
  },
  {
    exact corresponding_strings_drop n ass,
  },
end

end correspondence_for_terminals


section unwrapping_nst

private def unwrap_symbol₁ {N₁ N₂ : Type} : nst T N₁ N₂ → option (symbol T N₁)
| (symbol.terminal t)                               := some (symbol.terminal t)
| (symbol.nonterminal (sum.inr (sum.inl a)))        := some (symbol.terminal a)
| (symbol.nonterminal (sum.inr (sum.inr a)))        := none
| (symbol.nonterminal (sum.inl (some (sum.inl n)))) := some (symbol.nonterminal n)
| (symbol.nonterminal (sum.inl (some (sum.inr n)))) := none
| (symbol.nonterminal (sum.inl (none)))             := none

private def unwrap_symbol₂ {N₁ N₂ : Type} : nst T N₁ N₂ → option (symbol T N₂)
| (symbol.terminal t)                               := some (symbol.terminal t)
| (symbol.nonterminal (sum.inr (sum.inl a)))        := none
| (symbol.nonterminal (sum.inr (sum.inr a)))        := some (symbol.terminal a)
| (symbol.nonterminal (sum.inl (some (sum.inl n)))) := none
| (symbol.nonterminal (sum.inl (some (sum.inr n)))) := some (symbol.nonterminal n)
| (symbol.nonterminal (sum.inl (none)))             := none


private lemma unwrap_wrap₁_symbol {N₁ N₂ : Type} : @unwrap_symbol₁ T N₁ N₂ ∘ wrap_symbol₁ N₂ = option.some :=
begin
  ext1 a,
  cases a;
  refl,
end

private lemma unwrap_wrap₂_symbol {N₁ N₂ : Type} : @unwrap_symbol₂ T N₁ N₂ ∘ wrap_symbol₂ N₁ = option.some :=
begin
  ext1 a,
  cases a;
  refl,
end


private lemma unwrap_wrap₁_string {N₁ N₂ : Type} {w : list (symbol T N₁)} :
  list.filter_map unwrap_symbol₁ (list.map (wrap_symbol₁ N₂) w) = w :=
begin
  rw list.filter_map_map,
  rw unwrap_wrap₁_symbol,
  apply list.filter_map_some,
end

private lemma unwrap_wrap₂_string {N₁ N₂ : Type} {w : list (symbol T N₂)} :
  list.filter_map unwrap_symbol₂ (list.map (wrap_symbol₂ N₁) w) = w :=
begin
  rw list.filter_map_map,
  rw unwrap_wrap₂_symbol,
  apply list.filter_map_some,
end


private lemma unwrap_eq_some_of_corresponding_symbols₁ {N₁ N₂ : Type} {s₁ : symbol T N₁} {s : nst T N₁ N₂}
    (ass : corresponding_symbols (wrap_symbol₁ N₂ s₁) s) :
  unwrap_symbol₁ s = some s₁ :=
begin
  cases s₁;
  {
    unfold wrap_symbol₁ at ass,
    repeat {
      try {
        cases s,
      },
      try {
        unfold corresponding_symbols at ass,
        rw ass,
        refl,
      },
      try {
        unfold corresponding_symbols at ass,
        exfalso,
        exact ass,
      },
    },
  },
end

private lemma unwrap_eq_some_of_corresponding_symbols₂ {N₁ N₂ : Type} {s₂ : symbol T N₂} {s : nst T N₁ N₂}
    (ass : corresponding_symbols (wrap_symbol₂ N₁ s₂) s) :
  unwrap_symbol₂ s = some s₂ :=
begin
  cases s₂;
  {
    unfold wrap_symbol₂ at ass,
    repeat {
      try {
        cases s,
      },
      try {
        unfold corresponding_symbols at ass,
        rw ass,
        refl,
      },
      try {
        unfold corresponding_symbols at ass,
        exfalso,
        exact ass,
      },
    },
  },
end


private lemma map_unwrap_eq_map_some_of_corresponding_strings₁ {N₁ N₂ : Type} :
  ∀ {v : list (symbol T N₁)}, ∀ {w : list (nst T N₁ N₂)},
    corresponding_strings (list.map (wrap_symbol₁ N₂) v) w →
      list.map unwrap_symbol₁ w = list.map option.some v
| []     []     := λ _, rfl
| []     (b::y) := by { intro hyp, exfalso, unfold corresponding_strings at hyp, unfold list.map at hyp, finish, }
| (a::x) []     := by { intro hyp, exfalso, unfold corresponding_strings at hyp, unfold list.map at hyp, finish, }
| (a::x) (b::y) :=
begin
  intro ass,
  unfold corresponding_strings at ass,
  rw list.map_cons at ass,
  rw list.forall₂_cons at ass,
  rw list.map,
  rw list.map,
  apply congr_arg2,
  {
    exact unwrap_eq_some_of_corresponding_symbols₁ ass.1,
  },
  {
    apply map_unwrap_eq_map_some_of_corresponding_strings₁,
    exact ass.2
  },
end

private lemma map_unwrap_eq_map_some_of_corresponding_strings₂ {N₁ N₂ : Type} :
  ∀ {v : list (symbol T N₂)}, ∀ {w : list (nst T N₁ N₂)},
    corresponding_strings (list.map (wrap_symbol₂ N₁) v) w →
      list.map unwrap_symbol₂ w = list.map option.some v
| []     []     := λ _, rfl
| []     (b::y) := by { intro hyp, exfalso, unfold corresponding_strings at hyp, unfold list.map at hyp, finish, }
| (a::x) []     := by { intro hyp, exfalso, unfold corresponding_strings at hyp, unfold list.map at hyp, finish, }
| (a::x) (b::y) :=
begin
  intro ass,
  unfold corresponding_strings at ass,
  rw list.map_cons at ass,
  rw list.forall₂_cons at ass,
  rw list.map,
  rw list.map,
  apply congr_arg2,
  {
    exact unwrap_eq_some_of_corresponding_symbols₂ ass.1,
  },
  {
    apply map_unwrap_eq_map_some_of_corresponding_strings₂,
    exact ass.2
  },
end


private lemma filter_map_unwrap_of_corresponding_strings₁ {N₁ N₂ : Type}
    {v : list (symbol T N₁)} {w : list (nst T N₁ N₂)}
    (ass : corresponding_strings (list.map (wrap_symbol₁ N₂) v) w) :
  list.filter_map unwrap_symbol₁ w = v :=
begin
  apply list_filter_map_eq_of_map_eq_map_some,
  exact map_unwrap_eq_map_some_of_corresponding_strings₁ ass,
end

private lemma filter_map_unwrap_of_corresponding_strings₂ {N₁ N₂ : Type}
    {v : list (symbol T N₂)} {w : list (nst T N₁ N₂)}
    (ass : corresponding_strings (list.map (wrap_symbol₂ N₁) v) w) :
  list.filter_map unwrap_symbol₂ w = v :=
begin
  apply list_filter_map_eq_of_map_eq_map_some,
  exact map_unwrap_eq_map_some_of_corresponding_strings₂ ass,
end


private lemma corresponding_string_after_wrap_unwrap_self₁ {N₁ N₂ : Type} {w : list (nst T N₁ N₂)}
    (ass : ∃ z : list (symbol T N₁), corresponding_strings (list.map (wrap_symbol₁ N₂) z) w) :
  corresponding_strings (list.map (wrap_symbol₁ N₂) (list.filter_map unwrap_symbol₁ w)) w :=
begin
  induction w with d l ih,
  {
    unfold corresponding_strings,
    unfold list.filter_map,
    unfold list.map,
    exact list.forall₂.nil,
  },
  specialize ih (by {
    cases ass with z hyp,
    unfold corresponding_strings at *,
    cases z with z₀ z',
    {
      exfalso,
      finish,
    },
    {
      use z',
      finish,
    },
  }),
  unfold corresponding_strings,
  cases d,
  {
    have unwrap_first_t :
      list.filter_map unwrap_symbol₁ (symbol.terminal d :: l) =
      symbol.terminal d :: list.filter_map unwrap_symbol₁ l,
    {
      refl,
    },
    rw unwrap_first_t,
    unfold list.map,
    unfold wrap_symbol₁,
    rw list.forall₂_cons,
    split,
    {
      unfold corresponding_symbols,
    },
    {
      exact ih,
    },
  },
  cases d,
    cases d, swap,
      cases d,
      {
        have unwrap_first_nlsl :
          list.filter_map unwrap_symbol₁ (symbol.nonterminal (sum.inl (some (sum.inl d))) :: l) =
          symbol.nonterminal d :: list.filter_map unwrap_symbol₁ l,
        {
          refl,
        },
        rw unwrap_first_nlsl,
        unfold list.map,
        unfold wrap_symbol₁,
        rw list.forall₂_cons,
        split,
        {
          unfold corresponding_symbols,
        },
        {
          exact ih,
        },
      },
  swap 3,
    cases d,
    {
      have unwrap_first_nrl :
        list.filter_map unwrap_symbol₁ (symbol.nonterminal (sum.inr (sum.inl d)) :: l) =
        symbol.terminal d :: list.filter_map unwrap_symbol₁ l,
      {
        refl,
      },
      rw unwrap_first_nrl,
      unfold list.map,
      unfold wrap_symbol₁,
      rw list.forall₂_cons,
      split,
      {
        unfold corresponding_symbols,
      },
      {
        exact ih,
      },
    },
  any_goals {
    exfalso,
    cases ass with z hyp,
    cases z with z₀ z',
    {
      have imposs := corresponding_strings_length hyp,
      clear_except imposs,
      rw list.length at imposs,
      rw list.length_map at imposs,
      rw list.length at imposs,
      tauto,
    },
    {
      rw list.map_cons at hyp,
      unfold corresponding_strings at hyp,
      rw list.forall₂_cons at hyp,
      have impos := hyp.left,
      clear_except impos,
      cases z₀;
      {
        unfold wrap_symbol₁ at impos,
        unfold corresponding_symbols at impos,
        exact impos,
      },
    },
  },
end

private lemma corresponding_string_after_wrap_unwrap_self₂ {N₁ N₂ : Type} {w : list (nst T N₁ N₂)}
    (ass : ∃ z : list (symbol T N₂), corresponding_strings (list.map (wrap_symbol₂ N₁) z) w) :
  corresponding_strings (list.map (wrap_symbol₂ N₁) (list.filter_map unwrap_symbol₂ w)) w :=
begin
  induction w with d l ih,
  {
    unfold corresponding_strings,
    unfold list.filter_map,
    unfold list.map,
    exact list.forall₂.nil,
  },
  specialize ih (by {
    cases ass with z hyp,
    unfold corresponding_strings at *,
    cases z with z₀ z',
    {
      exfalso,
      finish,
    },
    {
      use z',
      finish,
    },
  }),
  unfold corresponding_strings,
  cases d,
  {
    have unwrap_first_t :
      list.filter_map unwrap_symbol₂ (symbol.terminal d :: l) =
      symbol.terminal d :: list.filter_map unwrap_symbol₂ l,
    {
      refl,
    },
    rw unwrap_first_t,
    unfold list.map,
    unfold wrap_symbol₂,
    rw list.forall₂_cons,
    split,
    {
      unfold corresponding_symbols,
    },
    {
      exact ih,
    },
  },
  cases d,
    cases d, swap,
      cases d, swap,
      {
        have unwrap_first_nlsr :
          list.filter_map unwrap_symbol₂ (symbol.nonterminal (sum.inl (some (sum.inr d))) :: l) =
          symbol.nonterminal d :: list.filter_map unwrap_symbol₂ l,
        {
          refl,
        },
        rw unwrap_first_nlsr,
        unfold list.map,
        unfold wrap_symbol₂,
        rw list.forall₂_cons,
        split,
        {
          unfold corresponding_symbols,
        },
        {
          exact ih,
        },
      },
  swap 3,
    cases d, swap,
    {
      have unwrap_first_nrr :
        list.filter_map unwrap_symbol₂ (symbol.nonterminal (sum.inr (sum.inr d)) :: l) =
        symbol.terminal d :: list.filter_map unwrap_symbol₂ l,
      {
        refl,
      },
      rw unwrap_first_nrr,
      unfold list.map,
      unfold wrap_symbol₂,
      rw list.forall₂_cons,
      split,
      {
        unfold corresponding_symbols,
      },
      {
        exact ih,
      },
    },
  any_goals {
    exfalso,
    cases ass with z hyp,
    cases z with z₀ z',
    {
      have imposs := corresponding_strings_length hyp,
      clear_except imposs,
      rw list.length at imposs,
      rw list.length_map at imposs,
      rw list.length at imposs,
      tauto,
    },
    {
      rw list.map_cons at hyp,
      unfold corresponding_strings at hyp,
      rw list.forall₂_cons at hyp,
      have impos := hyp.left,
      clear_except impos,
      cases z₀;
      {
        unfold wrap_symbol₂ at impos,
        unfold corresponding_symbols at impos,
        exact impos,
      },
    },
  },
end

end unwrapping_nst


section very_complicated

private lemma induction_step_for_lifted_rule_from_g₁
    {g₁ g₂ : grammar T}
    {a b u v : list (nst T g₁.nt g₂.nt)}
    {x : list (symbol T g₁.nt)}
    {y : list (symbol T g₂.nt)}
    {r : grule T (nnn T g₁.nt g₂.nt)}
    (rin : r ∈ list.map (wrap_grule₁ g₂.nt) g₁.rules)
    (bef : a = u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v)
    (aft : b = u ++ r.output_string ++ v)
    (ih_x : grammar_derives g₁ [symbol.nonterminal g₁.initial] x)
    (ih_y : grammar_derives g₂ [symbol.nonterminal g₂.initial] y)
    (ih_concat :
      corresponding_strings
        (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y)
        a) :
  ∃ (x' : list (symbol T g₁.nt)),
    and
      (and
        (grammar_derives g₁ [symbol.nonterminal g₁.initial] x')
        (grammar_derives g₂ [symbol.nonterminal g₂.initial] y)
      )
      (corresponding_strings (list.map (wrap_symbol₁ g₂.nt) x' ++ list.map (wrap_symbol₂ g₁.nt) y) b) :=
begin
  rw list.mem_map at rin,
  rcases rin with ⟨r₁, rin₁, wrap_r₁_eq_r⟩,
  rw ←wrap_r₁_eq_r at *,
  clear wrap_r₁_eq_r,
  simp [wrap_grule₁] at *,
  rw ←list.singleton_append at bef,

  let m := (list.map (wrap_symbol₁ g₂.nt) r₁.input_L).length + 1 +
           (list.map (wrap_symbol₁ g₂.nt) r₁.input_R).length,
  let b' := u ++ list.map (wrap_symbol₁ g₂.nt) r₁.output_string ++ list.take (x.length - u.length - m) v,
  use list.filter_map unwrap_symbol₁ b',

  have critical :
    (list.map (wrap_symbol₁ g₂.nt) r₁.input_L).length + 1 +
      (list.map (wrap_symbol₁ g₂.nt) r₁.input_R).length ≤
    x.length - u.length,
  {
    clear_except ih_concat bef,
    have as_positive :
      u.length + (
          (list.map (wrap_symbol₁ g₂.nt) r₁.input_L).length + 1 +
          (list.map (wrap_symbol₁ g₂.nt) r₁.input_R).length
        ) ≤
      x.length,
    {
      by_contradiction contra,
      push_neg at contra,
      rw bef at ih_concat,
      clear bef,
      repeat {
        rw ←list.append_assoc at ih_concat
      },
      have len_pos :
        (u ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
          [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_R
        ).length > 0,
      {
        repeat {
          rw list.length_append,
        },
        rw list.length_singleton,
        clear_except,
        linarith,
      },
      have equal_total_len := corresponding_strings_length ih_concat,

      have inequality_m1 :
        (u ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
          [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_R
        ).length - 1 <
        (u ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
          [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_R
        ).length,
      {
        exact buffer.lt_aux_2 len_pos,
      },
      have inequality_cat :
        (u ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
          [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_R
        ).length - 1 <
        (u ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
          [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_R ++ v
        ).length,
      {
        rw list.length_append _ v,
        apply lt_of_lt_of_le (buffer.lt_aux_2 len_pos),
        exact le_self_add,
      },
      have inequality_map :
        (u ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
          [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_R
        ).length - 1 <
        ((list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y)).length,
      {
        rw equal_total_len,
        exact inequality_cat,
      },
      have inequality_map_opp :
        (u ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
          [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_R
        ).length - 1 ≥
        (list.map (wrap_symbol₁ g₂.nt) x).length,
      {
        clear_except contra,
        apply nat.le_pred_of_lt,
        repeat {
          rw list.length_append,
        },
        repeat {
          rw list.length_map,
        },
        rw list.length_map at contra,
        rw list.length_map at contra,
        rw list.length_singleton,
        rw add_assoc,
        rw add_assoc,
        rw add_assoc at contra,
        exact contra,
      },
      have clash := corresponding_strings_nth_le inequality_map inequality_cat ih_concat,
      rw list.nth_le_append inequality_cat inequality_m1 at clash,
      rw list.nth_le_append_right inequality_map_opp inequality_map at clash,

      rw list.nth_le_map at clash, swap,
      {
        have inequality_map := inequality_map,
        rw list.length_append _ (list.map (wrap_symbol₂ g₁.nt) y) at inequality_map,
        rw list.length_map _ y at inequality_map,
        rw tsub_lt_iff_left inequality_map_opp,
        exact inequality_map,
      },
      by_cases (list.map (wrap_symbol₁ g₂.nt) r₁.input_R).length ≥ 1,
      {
        rw list.nth_le_append_right at clash, swap,
        {
          rw list.length_append _ (list.map (wrap_symbol₁ g₂.nt) r₁.input_R),
          have trivi_ineq : ∀ m k : ℕ, k ≥ 1 → m ≤ m + k - 1,
          {
            clear_except,
            omega,
          },
          convert trivi_ineq (u ++ _ ++ [_]).length _ h,
        },
        rw list.nth_le_map at clash, swap,
        {
          rw list.length_map at h,
          repeat {
            rw list.length_append,
          },
          repeat {
            rw list.length_map,
          },
          rw list.length_singleton,
          have easy_ineq : ∀ m k : ℕ, k ≥ 1 → m + k - 1 - m < k,
          {
            clear_except,
            omega,
          },
          convert easy_ineq (u.length + r₁.input_L.length + 1) _ h,
        },
        exact corresponding_symbols_never₂ clash,
      },
      {
        push_neg at h,
        have ris_third_is_nil : list.map (wrap_symbol₁ g₂.nt) r₁.input_R = [],
        {
          rw ←list.length_eq_zero,
          rw ←nat.lt_one_iff,
          exact h,
        },
        have inequality_m0 :
          (u ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
            [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))]).length - 1 <
          (u ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
            [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))]).length,
        {
          rw ris_third_is_nil at inequality_m1,
          rw list.append_nil at inequality_m1,
          exact inequality_m1,
        },
        have I_cannot_believe_I_had_to_write_it_explicitly :
          list.nth_le
            (u ++
              list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
              [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
              list.map (wrap_symbol₁ g₂.nt) r₁.input_R
            )
            (
              (u ++
                list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
                [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
                list.map (wrap_symbol₁ g₂.nt) r₁.input_R
              ).length - 1
            )
            inequality_m1 =
          list.nth_le
            (u ++
              list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
              [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))]
            )
            (
              (u ++
                list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
                [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))]
              ).length - 1
            )
            inequality_m0,
        {
          simp [ris_third_is_nil],
        },
        rw I_cannot_believe_I_had_to_write_it_explicitly at clash,
        rw list.nth_le_append_right at clash, swap,
        {
          apply le_of_eq,
          rw list.length_append _ [_],
          rw list.length_singleton,
          apply nat.succ_sub_one,
        },
        rw list.nth_le_singleton at clash,
        change
          corresponding_symbols _ (wrap_symbol₁ g₂.nt (symbol.nonterminal r₁.input_N)) at clash,
        exact corresponding_symbols_never₂ clash,
      },
    },
    omega,
  },

  split,
  {
    split,
    {
      apply grammar_deri_of_deri_tran ih_x,
      use r₁,
      split,
      {
        exact rin₁,
      },
      use list.filter_map unwrap_symbol₁ u,
      use list.filter_map unwrap_symbol₁ (list.take (x.length - u.length - m) v),
      split,
      {
        have x_equiv :
          corresponding_strings
            (list.map (wrap_symbol₁ g₂.nt) x)
            (list.take x.length (u
              ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L
              ++ [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))]
              ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_R
              ++ v)),
        {
          rw bef at ih_concat,
          clear_except ih_concat,
          rw ←list.append_assoc _ _ v at ih_concat,
          rw ←list.append_assoc _ _ v at ih_concat,
          rw list.append_assoc u,
          rw list.append_assoc u,
          rw list.append_assoc u,
          rw list.append_assoc (list.map (wrap_symbol₁ g₂.nt) r₁.input_L),

          convert corresponding_strings_take x.length ih_concat,
          {
            have x_len_eq : x.length = (list.map (wrap_symbol₁ g₂.nt) x).length,
            {
              rw list.length_map,
            },
            rw x_len_eq,
            rw list.take_left,
          },
        },
        clear_except x_equiv critical,

        have ul_le_xl : u.length ≤ x.length,
        {
          clear_except critical,
          have weaker_le : 1 ≤ x.length - u.length,
          {
            omega,
          },
          have stupid_le : u.length + 1 ≤ x.length,
          {
            omega,
          },
          exact nat.le_of_succ_le stupid_le,
        },
        repeat {
          rw list.take_append_eq_append_take at x_equiv,
        },
        rw list.take_all_of_le ul_le_xl at x_equiv,
        repeat {
          rw list.append_assoc,
        },

        have chunk2 :
          list.take (x.length - u.length) (list.map (wrap_symbol₁ g₂.nt) r₁.input_L) =
          list.map (wrap_symbol₁ g₂.nt) r₁.input_L,
        {
          apply list.take_all_of_le,
          clear_except critical,
          omega,
        },
        have chunk3 :
          list.take (x.length - (u ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L).length)
            [@symbol.nonterminal T (nnn T g₁.nt g₂.nt) (sum.inl (some (sum.inl r₁.input_N)))] =
          [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))],
        {
          apply list.take_all_of_le,
          clear_except critical,
          change 1 ≤ x.length - (u ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L).length,
          rw list.length_append,
          have weakened :
            (list.map (wrap_symbol₁ g₂.nt) r₁.input_L).length + 1 ≤
            x.length - u.length,
          {
            omega,
          },
          have goal_as_le_sub_sub :
            1 ≤ (x.length - u.length) - (list.map (wrap_symbol₁ g₂.nt) r₁.input_L).length,
          {
            omega,
          },
          rw tsub_add_eq_tsub_tsub,
          exact goal_as_le_sub_sub,
        },
        have chunk4 :
          list.take (x.length - (
              u ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
              [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))]
            ).length) (list.map (wrap_symbol₁ g₂.nt) r₁.input_R) =
          list.map (wrap_symbol₁ g₂.nt) r₁.input_R,
        {
          apply list.take_all_of_le,
          clear_except critical,
          rw list.length_append_append,
          change
            (list.map (wrap_symbol₁ g₂.nt) r₁.input_R).length ≤
            x.length - (u.length + (list.map (wrap_symbol₁ g₂.nt) r₁.input_L).length + 1),
          omega,
        },
        have chunk5 :
          list.take (x.length - (
              u ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
              [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
              list.map (wrap_symbol₁ g₂.nt) r₁.input_R).length
            ) v =
          list.take (x.length - u.length - m) v,
        {
          repeat {
            rw list.length_append,
          },
          apply congr_arg2, swap,
          {
            refl,
          },
          have rearrange_sum_of_four : ∀ a b c d : ℕ, a + b + c + d = a + (b + c + d),
          {
            omega,
          },
          rw rearrange_sum_of_four,
          change x.length - (u.length + m) = x.length - u.length - m,
          clear_except,
          omega,
        },
        rw [chunk2, chunk3, chunk4, chunk5] at x_equiv,
        clear chunk2 chunk3 chunk4 chunk5,

        obtain ⟨foo, equiv_segment_5⟩ :=
          corresponding_strings_split (
              u ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
              [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
              list.map (wrap_symbol₁ g₂.nt) r₁.input_R
            ).length x_equiv,
        clear x_equiv,
        rw list.drop_left at equiv_segment_5,
        rw list.take_left at foo,

        obtain ⟨bar, equiv_segment_4⟩ :=
          corresponding_strings_split (
              u ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
              [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))]
            ).length foo,
        clear foo,
        rw list.drop_left at equiv_segment_4,
        rw list.take_left at bar,
        rw list.take_take at bar,

        obtain ⟨baz, equiv_segment_3⟩ :=
          corresponding_strings_split (
              u ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_L
            ).length bar,
        clear bar,
        rw list.drop_left at equiv_segment_3,
        rw list.take_left at baz,
        rw list.take_take at baz,

        obtain ⟨equiv_segment_1, equiv_segment_2⟩ :=
          corresponding_strings_split u.length baz,
        clear baz,
        rw list.drop_left at equiv_segment_2,
        rw list.take_left at equiv_segment_1,
        rw list.take_take at equiv_segment_1,

        -- This `simp` is dangerous. See `RE_concatenation_RE_simp_goal.txt` for intended result.
        simp at equiv_segment_1 equiv_segment_2 equiv_segment_3 equiv_segment_4 equiv_segment_5,

        have segment_1_eqi : corresponding_strings (list.map (wrap_symbol₁ g₂.nt) (list.take u.length x)) u,
        {
          convert equiv_segment_1,
          rw list.map_take,
        },
        have segment_1_equ := (filter_map_unwrap_of_corresponding_strings₁ segment_1_eqi).symm,
        rw ←list.take_append_drop u.length x,
        apply congr_arg2,
        {
          exact segment_1_equ,
        },
        clear segment_1_equ segment_1_eqi equiv_segment_1,

        have segment_2_eqi :
          corresponding_strings
            (list.map (wrap_symbol₁ g₂.nt) (list.take r₁.input_L.length (list.drop u.length x)))
            (list.map (wrap_symbol₁ g₂.nt) r₁.input_L),
        {
          convert equiv_segment_2,
          rw list.map_take,
          rw list.map_drop,
          rw list.drop_take,
        },
        have segment_2_equ := (filter_map_unwrap_of_corresponding_strings₁ segment_2_eqi).symm,
        rw unwrap_wrap₁_string at segment_2_equ,
        rw ←list.take_append_drop r₁.input_L.length (list.drop u.length x),
        apply congr_arg2,
        {
          exact segment_2_equ,
        },
        clear segment_2_equ segment_2_eqi equiv_segment_2,
        rw list.drop_drop,

        have segment_3_eqi :
          corresponding_strings
            (list.map (wrap_symbol₁ g₂.nt) (list.take 1 (list.drop (r₁.input_L.length + u.length) x)))
            (list.map (wrap_symbol₁ g₂.nt) [symbol.nonterminal r₁.input_N]),
        {
          convert equiv_segment_3,
          rw list.map_take,
          rw list.map_drop,
          rw ←add_assoc,
          rw list.drop_take,
          rw add_comm,
        },
        have segment_3_equ := (filter_map_unwrap_of_corresponding_strings₁ segment_3_eqi).symm,
        rw unwrap_wrap₁_string at segment_3_equ,
        rw ←list.take_append_drop 1 (list.drop (r₁.input_L.length + u.length) x),
        apply congr_arg2,
        {
          exact segment_3_equ,
        },
        clear segment_3_equ segment_3_eqi equiv_segment_3,
        rw list.drop_drop,

        have segment_4_eqi :
          corresponding_strings
            (list.map (wrap_symbol₁ g₂.nt) (list.take r₁.input_R.length
              (list.drop (1 + (r₁.input_L.length + u.length)) x)))
            (list.map (wrap_symbol₁ g₂.nt) r₁.input_R),
        {
          convert equiv_segment_4,
          rw list.map_take,
          rw list.map_drop,

          have sum_rearrange :
            u.length + (r₁.input_L.length + (r₁.input_R.length + 1)) =
            (u.length + (r₁.input_L.length + 1)) + r₁.input_R.length,
          {
            linarith,
          },
          rw sum_rearrange,
          rw list.drop_take,

          have small_sum_rearr :
            1 + (r₁.input_L.length + u.length) =
            u.length + (r₁.input_L.length + 1),
          {
            linarith,
          },
          rw small_sum_rearr,
        },
        have segment_4_equ := (filter_map_unwrap_of_corresponding_strings₁ segment_4_eqi).symm,
        rw unwrap_wrap₁_string at segment_4_equ,
        rw ←list.take_append_drop r₁.input_R.length
          (list.drop (1 + (r₁.input_L.length + u.length)) x),
        apply congr_arg2,
        {
          exact segment_4_equ,
        },
        clear segment_4_equ segment_4_eqi equiv_segment_4,

        rw list.drop_drop,
        repeat {
          rw list.length_append,
        },
        repeat {
          rw list.length_take,
        },
        repeat {
          rw list.length_drop,
        },

        have sum_of_min_lengths :
          min u.length x.length +
            (min r₁.input_L.length (x.length - u.length) +
            (min 1 (x.length - (r₁.input_L.length + u.length)) +
            (min r₁.input_R.length (x.length - (1 + (r₁.input_L.length + u.length))) +
            (x.length - (r₁.input_R.length + (1 + (r₁.input_L.length + u.length))))))) =
          x.length,
        {
          have add_mirror :
            r₁.input_R.length + 1 + r₁.input_L.length =
            r₁.input_L.length + 1 + r₁.input_R.length,
          {
            ring,
          },
          rw [list.length_map, list.length_map, ←add_mirror] at critical,

          have min1 : min u.length x.length = u.length,
          {
            apply min_eq_left,
            exact ul_le_xl,
          },
          have min2 : min r₁.input_L.length (x.length - u.length) = r₁.input_L.length,
          {
            clear_except critical,
            apply min_eq_left,
            apply le_trans _ critical,
            apply le_add_self,
          },
          have min3 : min 1 (x.length - (r₁.input_L.length + u.length)) = 1,
          {
            clear_except critical,
            apply min_eq_left,
            omega,
          },
          have min4 :
            min r₁.input_R.length (x.length - (1 + (r₁.input_L.length + u.length))) =
            r₁.input_R.length,
          {
            clear_except critical,
            apply min_eq_left,
            omega,
          },
          rw [min1, min2, min3, min4],
          rw le_tsub_iff_right ul_le_xl at critical,
          clear_except critical add_mirror,
          repeat {
            rw ←add_assoc,
          },
          have sum_eq_sum :
            u.length + r₁.input_L.length + 1 + r₁.input_R.length =
            r₁.input_R.length + 1 + r₁.input_L.length + u.length,
          {
            rw add_mirror,
            rw add_assoc,
            rw add_assoc,
            rw add_comm,
            rw ←add_assoc _ 1 _,
          },
          rw sum_eq_sum,
          exact nat.add_sub_of_le critical,
        },
        rw sum_of_min_lengths,
        clear_except equiv_segment_5,

        have another_rearranging :
          r₁.input_R.length + (1 + (r₁.input_L.length + u.length)) =
          u.length + (r₁.input_L.length + (r₁.input_R.length + 1)),
        {
          ring,
        },
        rw another_rearranging,
        rw ←list.map_drop at equiv_segment_5,
        symmetry,
        exact filter_map_unwrap_of_corresponding_strings₁ equiv_segment_5,
      },
      {
        rw list.filter_map_append_append,
        congr,
        rw unwrap_wrap₁_string,
      },
    },
    {
      exact ih_y,
    },
  },
  rw aft,
  rw bef at ih_concat,
  rw list.filter_map_append_append,
  rw list.map_append_append,
  rw list.append_assoc,
  rw list.append_assoc,

  apply corresponding_strings_append,
  {
    have part_for_u := corresponding_strings_take u.length ih_concat,
    rw list.take_left at part_for_u,
    have trivi : u.length ≤ (list.map (wrap_symbol₁ g₂.nt) x).length,
    {
      clear_except critical,
      rw list.length_map,
      omega,
    },
    rw list.take_append_of_le_length trivi at part_for_u,
    clear_except part_for_u,
    rw ←list.map_take at part_for_u,
    apply corresponding_string_after_wrap_unwrap_self₁,
    use list.take u.length x,
    exact part_for_u,
  },
  apply corresponding_strings_append,
  {
    rw unwrap_wrap₁_string,
    apply corresponding_strings_self,
  },
  convert_to
    corresponding_strings _ (list.take (x.length - u.length - m) v ++ list.drop (x.length - u.length - m) v),
  {
    rw list.take_append_drop,
  },
  apply corresponding_strings_append,
  {
    have eqi := corresponding_strings_take (list.map (wrap_symbol₁ g₂.nt) x).length ih_concat,
    rw list.take_left at eqi,
    have part_for_v_beginning := corresponding_strings_drop (u.length + m) eqi,
    clear_except part_for_v_beginning critical,
    rw ←list.map_drop at part_for_v_beginning,
    apply corresponding_string_after_wrap_unwrap_self₁,
    use list.drop (u.length + m) x,
    convert part_for_v_beginning,
    clear part_for_v_beginning,
    rw list.length_map,
    rw list.take_append_eq_append_take,
    rw list.drop_append_eq_append_drop,
    have tul_lt : (list.take x.length u).length ≤ u.length + m,
    {
      rw list.length_take,
      calc min x.length u.length
          ≤ u.length     : min_le_right _ _
      ... ≤ u.length + m : le_self_add,
    },
    rw list.drop_eq_nil_of_le tul_lt,
    rw list.nil_append,
    rw ←list.append_assoc _ _ v,
    rw ←list.append_assoc _ _ v,
    rw ←list.append_assoc,
    rw list.take_append_eq_append_take,
    rw list.drop_append_eq_append_drop,
    have rul_inp_len :
      (list.map (wrap_symbol₁ g₂.nt) r₁.input_L ++
          [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_N)))] ++
          list.map (wrap_symbol₁ g₂.nt) r₁.input_R
        ).length = m,
    {
      rw list.length_append_append,
      rw list.length_singleton,
    },
    have u_is_shorter : min x.length u.length = u.length,
    {
      apply min_eq_right,
      clear_except critical,
      omega,
    },
    rw list.drop_eq_nil_of_le, swap,
    {
      rw list.length_take,
      rw rul_inp_len,
      rw list.length_take,
      rw u_is_shorter,
      calc min (x.length - u.length) m ≤ m : min_le_right _ _
      ... ≤ u.length + m - u.length        : le_add_tsub_swap,
    },
    rw list.nil_append,
    rw list.length_take,
    rw list.length_take,
    rw rul_inp_len,
    have zero_dropping : u.length + m - min x.length u.length - min (x.length - u.length) m = 0,
    {
      have middle_cannot_exceed : min (x.length - u.length) m = m,
      {
        exact min_eq_right critical,
      },
      rw [u_is_shorter, middle_cannot_exceed],
      clear_except,
      omega,
    },
    rw zero_dropping,
    unfold list.drop,
  },
  -- now we have what `g₂` generated
  have reverse_concat := corresponding_strings_reverse ih_concat,
  repeat {
    rw list.reverse_append at reverse_concat,
  },
  have the_part := corresponding_strings_take y.length reverse_concat,
  apply corresponding_strings_of_reverse,

  have len_sum : y.length + (x.length - u.length - m) = v.length,
  {
    change
      y.length + (x.length - u.length - (
        (list.map (wrap_symbol₁ g₂.nt) r₁.input_L).length + 1 +
        (list.map (wrap_symbol₁ g₂.nt) r₁.input_R).length
      )) =
      v.length,
    have len_concat := corresponding_strings_length ih_concat,
    clear_except len_concat critical,
    repeat {
      rw list.length_append at len_concat,
    },
    rw list.length_map at len_concat,
    rw list.length_map at len_concat,
    rw list.length_singleton at len_concat,
    rw ←nat.add_sub_assoc, swap,
    {
      exact critical,
    },
    rw ←nat.add_sub_assoc, swap,
    {
      clear_except critical,
      omega,
    },
    rw add_comm at len_concat,
    rw len_concat,
    clear len_concat,
    rw add_tsub_cancel_left,
    rw ←nat.add_assoc,
    rw ←nat.add_assoc,
    rw add_tsub_cancel_left,
  },
  have yl_lt_vl : y.length ≤ v.length,
  {
    exact nat.le.intro len_sum,
  },
  convert_to corresponding_strings _ (list.take y.length v.reverse),
  {
    convert_to (list.drop (v.length - y.length) v).reverse = list.take y.length v.reverse,
    {
      apply congr_arg,
      apply congr_arg2,
      {
        clear_except len_sum,
        omega,
      },
      {
        refl,
      },
    },
    rw list.reverse_take,
    exact yl_lt_vl,
  },
  clear_except the_part yl_lt_vl,
  rw list.take_append_of_le_length at the_part, swap,
  {
    rw list.length_reverse,
    rw list.length_map,
  },
  repeat {
    rw list.append_assoc at the_part,
  },
  rw list.take_append_of_le_length at the_part, swap,
  {
    rw list.length_reverse,
    exact yl_lt_vl,
  },
  rw list.take_all_of_le at the_part, swap,
  {
    rw list.length_reverse,
    rw list.length_map,
  },
  exact the_part,
end

private lemma induction_step_for_lifted_rule_from_g₂
    {g₁ g₂ : grammar T}
    {a b u v : list (nst T g₁.nt g₂.nt)}
    {x : list (symbol T g₁.nt)}
    {y : list (symbol T g₂.nt)}
    {r : grule T (nnn T g₁.nt g₂.nt)}
    (rin : r ∈ list.map (wrap_grule₂ g₁.nt) g₂.rules)
    (bef : a = u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v)
    (aft : b = u ++ r.output_string ++ v)
    (ih_x : grammar_derives g₁ [symbol.nonterminal g₁.initial] x)
    (ih_y : grammar_derives g₂ [symbol.nonterminal g₂.initial] y)
    (ih_concat :
      corresponding_strings
        (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y)
        a) :
  ∃ (y' : list (symbol T g₂.nt)),
    and
      (and
        (grammar_derives g₁ [symbol.nonterminal g₁.initial] x)
        (grammar_derives g₂ [symbol.nonterminal g₂.initial] y')
      )
      (corresponding_strings (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y') b) :=
begin
  rw list.mem_map at rin,
  rcases rin with ⟨r₂, rin₂, wrap_r₂_eq_r⟩,
  rw ←wrap_r₂_eq_r at *,
  clear wrap_r₂_eq_r,
  simp [wrap_grule₂] at *,
  rw ←list.singleton_append at bef,
  rw bef at ih_concat,

  let b' := list.drop x.length u ++ list.map (wrap_symbol₂ g₁.nt) r₂.output_string ++ v,
  use list.filter_map unwrap_symbol₂ b',

  have total_len := corresponding_strings_length ih_concat,
  repeat {
    rw list.length_append at total_len,
  },
  repeat {
    rw list.length_map at total_len,
  },

  have matched_right : u.length ≥ x.length,
  {
    clear_except ih_concat total_len,
    by_contradiction,
    push_neg at h,
    rename h ul_lt_xl,
    have ul_lt_ihls : u.length < (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).length,
    {
      rw list.length_append,
      rw list.length_map,
      rw list.length_map,
      exact nat.lt_add_right _ _ _ ul_lt_xl,
    },
    have ul_lt_ihrs :
      u.length <
      (u
        ++ (list.map (wrap_symbol₂ g₁.nt) r₂.input_L
        ++ ([symbol.nonterminal (sum.inl (some (sum.inr r₂.input_N)))]
        ++ (list.map (wrap_symbol₂ g₁.nt) r₂.input_R
        ++ v)))
      ).length,
    {
      repeat {
        rw list.length_append,
      },
      rw list.length_singleton,
      clear_except,
      linarith,
    },
    have ulth := corresponding_strings_nth_le ul_lt_ihls ul_lt_ihrs ih_concat,
    rw list.nth_le_append ul_lt_ihls at ulth, swap,
    {
      rw list.length_map,
      exact ul_lt_xl,
    },
    rw list.nth_le_append_right at ulth, swap,
    {
      refl,
    },
    rw list.nth_le_map at ulth, swap,
    {
      exact ul_lt_xl,
    },

    by_cases (list.map (wrap_symbol₂ g₁.nt) r₂.input_L).length > u.length - u.length,
    {
      rw list.nth_le_append _ h at ulth,
      rw list.nth_le_map at ulth, swap,
      {
        rw list.length_map at h,
        exact h,
      },
      exact corresponding_symbols_never₁ ulth,
    },
    push_neg at h,
    rw list.nth_le_append_right h at ulth,
    have matched_central_nt :
      corresponding_symbols
        (wrap_symbol₁ g₂.nt (x.nth_le u.length ul_lt_xl))
        (wrap_symbol₂ g₁.nt (symbol.nonterminal r₂.input_N)),
    {
      clear_except ulth,
      finish,
    },
    exact corresponding_symbols_never₁ matched_central_nt,
  },

  split,
  {
    split,
    {
      exact ih_x,
    },
    {
      apply grammar_deri_of_deri_tran ih_y,
      use r₂,
      split,
      {
        exact rin₂,
      },
      use list.filter_map unwrap_symbol₂ (list.drop x.length u),
      use list.filter_map unwrap_symbol₂ v,
      split,
      {
        have corres_y := corresponding_strings_drop (list.map (wrap_symbol₁ g₂.nt) x).length ih_concat,
        rw list.drop_left at corres_y,
        rw list.drop_append_of_le_length at corres_y, swap,
        {
          rw list.length_map,
          exact matched_right,
        },
        clear_except corres_y total_len,
        repeat {
          rw list.append_assoc,
        },

        obtain ⟨seg1, rest1⟩ :=
          corresponding_strings_split
            (list.drop (list.map (wrap_symbol₁ g₂.nt) x).length u).length
            corres_y,
        clear corres_y,
        rw list.take_left at seg1,
        rw list.drop_left at rest1,
        rw ←list.take_append_drop (list.filter_map unwrap_symbol₂ (list.drop x.length u)).length y,
        rw ←list.map_take at seg1,
        have min_uxy : min (u.length - x.length) y.length = u.length - x.length,
        {
          rw min_eq_left,
          clear_except total_len,
          omega,
        },
        have tuxy : list.take (list.take (u.length - x.length) y).length y = list.take (u.length - x.length) y,
        {
          rw list.length_take,
          rw min_uxy,
        },
        have fmu1 := filter_map_unwrap_of_corresponding_strings₂ seg1,
        rw list.length_map at fmu1,
        have fml :
          (list.filter_map unwrap_symbol₂ (list.drop x.length u)).length =
          (list.drop x.length u).length,
        {
          rw congr_arg list.length fmu1,
          rw list.length_take at tuxy,
          rw list.length_drop,
          rw min_uxy at tuxy,
          rw congr_arg list.length tuxy,
          rw list.length_take,
          exact min_uxy,
        },
        apply congr_arg2,
        {
          rw fmu1,
          rw list.length_drop,
          exact tuxy,
        },
        clear seg1 fmu1 tuxy min_uxy,

        rw list.length_map at rest1,
        obtain ⟨seg2, rest2⟩ :=
          corresponding_strings_split
            (list.map (wrap_symbol₂ g₁.nt) r₂.input_L).length
            rest1,
        clear rest1,
        rw list.take_left at seg2,
        rw list.drop_left at rest2,
        rw ←list.take_append_drop
          (list.map (wrap_symbol₂ g₁.nt) r₂.input_L).length
          (list.drop (list.filter_map unwrap_symbol₂ (list.drop x.length u)).length y),
        apply congr_arg2,
        {
          clear_except seg2 fml,
          rw ←list.map_drop at seg2,
          rw ←list.map_take at seg2,
          have fmu2 := filter_map_unwrap_of_corresponding_strings₂ seg2,
          rw list.length_map at fmu2,
          rw list.length_map,
          rw unwrap_wrap₂_string at fmu2,
          rw fml,
          exact fmu2.symm,
        },
        clear seg2,

        rw list.length_map at rest2,
        rw list.drop_drop at rest2 ⊢,
        obtain ⟨seg3, rest3⟩ :=
          corresponding_strings_split 1 rest2,
        clear rest2,
        rw list.take_left' (list.length_singleton _) at seg3,
        rw list.drop_left' (list.length_singleton _) at rest3,
        rw list.length_map,
        rw fml,
        rw ←list.take_append_drop
          1
          (list.drop (r₂.input_L.length + (list.drop x.length u).length) y),
        apply congr_arg2,
        {
          rw ←list.map_drop at seg3,
          rw ←list.map_take at seg3,
          have fmu3 := filter_map_unwrap_of_corresponding_strings₂ seg3,
          exact fmu3.symm,
        },
        clear seg3,

        rw list.drop_drop at rest3 ⊢,
        rw ←list.map_drop at rest3,
        rw ←filter_map_unwrap_of_corresponding_strings₂ rest3,
        rw list.filter_map_append,
        rw unwrap_wrap₂_string,
      },
      {
        rw list.filter_map_append_append,
        congr,
        apply unwrap_wrap₂_string,
      }
    },
  },
  rw aft,
  rw list.filter_map_append_append,
  rw list.map_append_append,
  rw list.append_assoc,
  rw ←list.append_assoc (list.map (wrap_symbol₁ g₂.nt) x),

  apply corresponding_strings_append, swap,
  {
    rw unwrap_wrap₂_string,
    apply corresponding_strings_append,
    {
      apply corresponding_strings_self,
    },
    apply corresponding_string_after_wrap_unwrap_self₂,
    repeat {
      rw ←list.append_assoc at ih_concat,
    },
    have rev := corresponding_strings_reverse ih_concat,
    rw list.reverse_append _ v at rev,
    have tak := corresponding_strings_take v.reverse.length rev,
    rw list.take_left at tak,
    have rtr := corresponding_strings_reverse tak,
    have nec : v.reverse.length ≤ (list.map (wrap_symbol₂ g₁.nt) y).reverse.length,
    {
      clear_except matched_right total_len,
      rw list.length_reverse,
      rw list.length_reverse,
      rw list.length_map,
      linarith,
    },
    clear_except rtr nec,

    rw list.reverse_reverse at rtr,
    rw list.reverse_append at rtr,
    rw list.take_append_of_le_length nec at rtr,
    rw list.reverse_take at rtr, swap,
    {
      rw list.length_reverse (list.map (wrap_symbol₂ g₁.nt) y) at nec,
      exact nec,
    },
    rw ←list.map_drop at rtr,
    rw list.reverse_reverse at rtr,
    exact ⟨_, rtr⟩,
  },
  rw ←list.take_append_drop x.length u,
  apply corresponding_strings_append,
  {
    have almost := corresponding_strings_take x.length ih_concat,
    rw list.take_append_of_le_length matched_right at almost,
    convert almost,
    have xl_eq : x.length = (list.map (wrap_symbol₁ g₂.nt) x).length,
    {
      rw list.length_map,
    },
    rw xl_eq,
    rw list.take_left,
  },
  {
    rw list.take_append_drop,
    apply corresponding_string_after_wrap_unwrap_self₂,
    have tdc := corresponding_strings_drop x.length (corresponding_strings_take u.length ih_concat),
    rw list.take_left at tdc,
    have ul_eq : u.length = x.length + (u.length - x.length),
    {
      rw ←nat.add_sub_assoc matched_right,
      rw add_comm,
      rw nat.add_sub_assoc, swap,
      {
        refl,
      },
      rw nat.sub_self,
      rw add_zero,
    },
    rw ul_eq at tdc,
    clear_except tdc,

    rw list.drop_take at tdc,
    rw list.drop_left' at tdc, swap,
    {
      apply list.length_map,
    },
    rw ←list.map_take at tdc,
    exact ⟨_, tdc⟩,
  },
end

private lemma big_induction
    {g₁ g₂ : grammar T}
    {w : list (nst T g₁.nt g₂.nt)}
    (ass :
      grammar_derives (big_grammar g₁ g₂)
        [symbol.nonterminal (sum.inl (some (sum.inl g₁.initial))),
        symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]
        w) :
  ∃ x : list (symbol T g₁.nt),
  ∃ y : list (symbol T g₂.nt),
    and
      (and
        (grammar_derives g₁ [symbol.nonterminal g₁.initial] x)
        (grammar_derives g₂ [symbol.nonterminal g₂.initial] y)
      )
      (corresponding_strings (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) w) :=
begin
  induction ass with a b trash orig ih,
  {
    use [[symbol.nonterminal g₁.initial], [symbol.nonterminal g₂.initial]],
    split,
    {
      split;
      apply grammar_deri_self,
    },
    {
      rw list.map_singleton,
      rw list.map_singleton,
      unfold wrap_symbol₁,
      unfold wrap_symbol₂,
      rw list.singleton_append,
      unfold corresponding_strings,
      rw list.forall₂_cons,
      split,
      {
        unfold corresponding_symbols,
      },
      rw list.forall₂_cons,
      split,
      {
        unfold corresponding_symbols,
      },
      exact list.forall₂.nil,
    },
  },
  rcases ih with ⟨x, y, ⟨ih_x, ih_y⟩, ih_concat⟩,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,
  change _ ∈ list.cons _ _ at rin,
  rw list.mem_cons_eq at rin,
  cases rin,
  {
    exfalso,
    rw rin at bef,
    clear_except ih_concat bef,
    simp only [list.append_nil] at bef,
    rw bef at ih_concat,
    have same_lengths := corresponding_strings_length ih_concat,
    clear bef,
    have ulen₁ : u.length < (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).length,
    {
      rw list.length_append _ v at same_lengths,
      rw list.length_append u _ at same_lengths,
      rw list.length_singleton at same_lengths,
      clear_except same_lengths,
      linarith,
    },
    have ulen₂ : u.length < (u ++ ([symbol.nonterminal (sum.inl none)] ++ v)).length,
    {
      rw list.length_append,
      rw list.length_append,
      rw list.length_singleton,
      clear_except,
      linarith,
    },
    have ulen_tauto : u.length ≤ u.length,
    {
      refl,
    },
    rw list.append_assoc at ih_concat,
    have eqi_symb := corresponding_strings_nth_le ulen₁ ulen₂ ih_concat,
    rw list.nth_le_append_right ulen_tauto at eqi_symb,
    simp only [nat.sub_self, list.singleton_append, list.nth_le] at eqi_symb,
    have eq_none :
      (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).nth_le u.length ulen₁ =
      (symbol.nonterminal (sum.inl (none))),
    {
      clear_except eqi_symb,
      cases (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).nth_le u.length ulen₁ with t s,
      {
        exfalso,
        clear_except eqi_symb,
        tauto,
      },
      cases s,
      {
        cases s,
        {
          refl,
        },
        exfalso,
        clear_except eqi_symb,
        cases s;
        tauto,
      },
      {
        exfalso,
        clear_except eqi_symb,
        cases s;
        tauto,
      },
    },
    have impossible_in :
      symbol.nonterminal (sum.inl none) ∈
        (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y),
    {
      rw list.mem_iff_nth_le,
      use u.length,
      use ulen₁,
      exact eq_none,
    },
    rw list.mem_append at impossible_in,
    cases impossible_in;
    {
      rw list.mem_map at impossible_in,
      rcases impossible_in with ⟨s, -, contradic⟩,
      clear_except contradic,
      cases s;
      {
        repeat { injections_and_clear },
        tauto,
      },
    },
  },
  rw list.mem_append at rin,
  cases rin,
  {
    rw list.mem_append at rin,
    cases rin,
    {
      cases induction_step_for_lifted_rule_from_g₁ rin bef aft ih_x ih_y ih_concat with x' pros,
      exact ⟨x', y, pros⟩,
    },
    {
      use x,
      exact induction_step_for_lifted_rule_from_g₂ rin bef aft ih_x ih_y ih_concat,
    }
  },
  {
    use [x, y],
    split,
    {
      split,
      {
        exact ih_x,
      },
      {
        exact ih_y,
      },
    },
    rw aft,
    rw bef at ih_concat,

    rw list.mem_append at rin,
    cases rin,
    {
      unfold rules_for_terminals₁ at rin,
      rw list.mem_map at rin,
      rcases rin with ⟨t, -, eq_r⟩,
      rw ←eq_r at *,
      clear eq_r,
      rw list.append_nil at ih_concat,
      rw list.append_nil at ih_concat,

      have xy_split_u :
        list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y =
          list.take u.length (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) ++
          list.drop u.length (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y),
      {
        rw list.take_append_drop,
      },
      rw xy_split_u,
      have part_for_u := corresponding_strings_take u.length ih_concat,
      rw list.append_assoc,
      apply corresponding_strings_append,
      {
        convert part_for_u,
        rw list.append_assoc,
        rw list.take_left,
      },
      have ul_lt_len_um : u.length < (u ++ [symbol.nonterminal (sum.inr (sum.inl t))]).length,
      {
        rw list.length_append,
        rw list.length_singleton,
        apply lt_add_one,
      },
      have ul_lt_len_umv : u.length < (u ++ [symbol.nonterminal (sum.inr (sum.inl t))] ++ v).length,
      {
        rw list.length_append,
        apply lt_of_lt_of_le ul_lt_len_um,
        apply le_self_add,
      },
      have ul_lt_len_xy : u.length < (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).length,
      {
        have same_len := corresponding_strings_length ih_concat,
        rw same_len,
        exact ul_lt_len_umv,
      },
      have middle_nt := corresponding_strings_nth_le ul_lt_len_xy ul_lt_len_umv ih_concat,
      rw list.nth_le_append ul_lt_len_umv ul_lt_len_um at middle_nt,
      rw list.nth_le_append_right (by refl) ul_lt_len_um at middle_nt,
      have middle_nt_elem :
        corresponding_symbols
          ((list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).nth_le u.length ul_lt_len_xy)
          (symbol.nonterminal (sum.inr (sum.inl t))),
      {
        convert middle_nt,
        finish,
      },
      have xy_split_nt :
        list.drop u.length (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) =
          list.take 1 (list.drop u.length (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y)) ++
          list.drop 1 (list.drop u.length (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y)),
      {
        rw list.take_append_drop,
      },
      rw xy_split_nt,
      apply corresponding_strings_append, swap,
      {
        rw list.drop_drop,
        have part_for_v := corresponding_strings_drop (1 + u.length) ih_concat,
        convert part_for_v,
        have correct_len : 1 + u.length = (u ++ [symbol.nonterminal (sum.inr (sum.inl t))]).length,
        {
          rw add_comm,
          rw list.length_append,
          rw list.length_singleton,
        },
        rw correct_len,
        rw list.drop_left,
      },
      {
        convert_to
          corresponding_strings
            [list.nth_le (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) u.length ul_lt_len_xy]
            [symbol.terminal t],
        {
          apply list.take_one_drop,
        },
        clear_except middle_nt_elem,
        apply corresponding_strings_singleton,
        cases
          (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).nth_le
            u.length ul_lt_len_xy with e s,
        {
          exfalso,
          unfold corresponding_symbols at middle_nt_elem,
          exact middle_nt_elem,
        },
        cases s,
        {
          exfalso,
          cases s, swap,
            cases s,
          all_goals {
            unfold corresponding_symbols at middle_nt_elem,
            exact middle_nt_elem,
          },
        },
        {
          cases s,
          {
            unfold corresponding_symbols at middle_nt_elem,
            rw middle_nt_elem,
            unfold corresponding_symbols,
          },
          {
            exfalso,
            unfold corresponding_symbols at middle_nt_elem,
            exact middle_nt_elem,
          },
        }
      },
    },
    {
      unfold rules_for_terminals₂ at rin,
      rw list.mem_map at rin,
      rcases rin with ⟨t, -, eq_r⟩,
      rw ←eq_r at *,
      clear eq_r,
      rw list.append_nil at ih_concat,
      rw list.append_nil at ih_concat,

      have xy_split_v :
        list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y =
          list.take (u.length + 1) (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) ++
          list.drop (u.length + 1) (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y),
      {
        rw list.take_append_drop,
      },
      rw xy_split_v,
      have part_for_v := corresponding_strings_drop (u.length + 1) ih_concat,
      apply corresponding_strings_append, swap,
      {
        convert part_for_v,
        have rewr_len : u.length + 1 = (u ++ [symbol.nonterminal (sum.inr (sum.inr t))]).length,
        {
          rw list.length_append,
          rw list.length_singleton,
        },
        rw rewr_len,
        rw list.drop_left,
      },
      have ul_lt_len_um : u.length < (u ++ [symbol.nonterminal (sum.inr (sum.inr t))]).length,
      {
        rw list.length_append,
        rw list.length_singleton,
        apply lt_add_one,
      },
      have ul_lt_len_umv : u.length < (u ++ [symbol.nonterminal (sum.inr (sum.inr t))] ++ v).length,
      {
        rw list.length_append,
        apply lt_of_lt_of_le ul_lt_len_um,
        apply le_self_add,
      },
      have ul_lt_len_xy : u.length < (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).length,
      {
        have same_len := corresponding_strings_length ih_concat,
        rw same_len,
        exact ul_lt_len_umv,
      },
      have middle_nt := corresponding_strings_nth_le ul_lt_len_xy ul_lt_len_umv ih_concat,
      rw list.nth_le_append ul_lt_len_umv ul_lt_len_um at middle_nt,
      rw list.nth_le_append_right (by refl) ul_lt_len_um at middle_nt,
      have middle_nt_elem :
        corresponding_symbols
          ((list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).nth_le u.length ul_lt_len_xy)
          (symbol.nonterminal (sum.inr (sum.inr t))),
      {
        convert middle_nt,
        finish,
      },
      have xy_split_nt :
        list.take (u.length + 1) (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) =
          list.take u.length (list.take (u.length + 1) (
              list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y)
            ) ++
          list.drop u.length (list.take (u.length + 1) (
              list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y)
            ),
      {
        rw list.take_append_drop u.length,
      },
      rw xy_split_nt,
      apply corresponding_strings_append,
      {
        rw list.take_take,
        have part_for_u := corresponding_strings_take u.length ih_concat,
        convert part_for_u,
        {
          apply min_eq_left,
          apply nat.le_succ,
        },
        rw list.append_assoc,
        rw list.take_left,
      },
      {
        convert_to
          corresponding_strings
            [list.nth_le (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) u.length ul_lt_len_xy]
            [symbol.terminal t],
        {
          apply list.drop_take_succ,
        },
        clear_except middle_nt_elem,
        apply corresponding_strings_singleton,
        cases
          (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).nth_le
            u.length ul_lt_len_xy with e s,
        {
          exfalso,
          unfold corresponding_symbols at middle_nt_elem,
          exact middle_nt_elem,
        },
        cases s,
        {
          exfalso,
          cases s, swap,
            cases s,
          all_goals {
            unfold corresponding_symbols at middle_nt_elem,
            exact middle_nt_elem,
          },
        },
        {
          cases s,
          {
            exfalso,
            unfold corresponding_symbols at middle_nt_elem,
            exact middle_nt_elem,
          },
          {
            unfold corresponding_symbols at middle_nt_elem,
            rw middle_nt_elem,
            unfold corresponding_symbols,
          },
        }
      },
    },
  },
end

protected lemma in_concatenated_of_in_big
    {g₁ g₂ : grammar T}
    {w : list T}
    (ass : w ∈ grammar_language (big_grammar g₁ g₂)) :
  w ∈ grammar_language g₁ * grammar_language g₂ :=
begin
  rw language.mem_mul,
  cases grammar_tran_or_id_of_deri ass,
  {
    exfalso,
    have nonmatch := congr_fun (congr_arg list.nth h) 0,
    clear_except nonmatch,
    unfold list.nth at nonmatch,
    cases w,
    {
      change some _ = none at nonmatch,
      tauto,
    },
    {
      unfold list.map at nonmatch,
      unfold list.nth at nonmatch,
      rw option.some.inj_eq at nonmatch,
      tauto,
    },
  },
  clear ass,
  rcases h with ⟨w₁, hyp_tran, hyp_deri⟩,
  have w₁eq : w₁ = [
      symbol.nonterminal (sum.inl (some (sum.inl g₁.initial))),
      symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))
    ],
  {
    clear_except hyp_tran,
    -- only the first rule is applicable
    rcases hyp_tran with ⟨r, rin, u, v, bef, aft⟩,

    have bef_len := congr_arg list.length bef,
    rw list.length_append_append at bef_len,
    rw list.length_append_append at bef_len,
    dsimp at bef_len,
    have u_nil : u = [], swap,
    have v_nil : v = [], swap,
    have rif_nil : r.input_L = [], swap,
    any_goals {
      clear_except bef_len,
      rw ←list.length_eq_zero,
      linarith,
    },

    change _ ∈ list.cons _ _ at rin,
    rw list.mem_cons_iff at rin,
    cases rin,
    {
      rw rin at bef aft,
      dsimp at bef aft,
      rw [u_nil, v_nil] at aft,
      rw [list.nil_append, list.append_nil] at aft,
      exact aft,
    },
    exfalso,
    have nt_match : symbol.nonterminal (big_grammar g₁ g₂).initial = symbol.nonterminal r.input_N,
    {
      have bef_fst := congr_fun (congr_arg list.nth bef) 0,
      rw [u_nil, rif_nil] at bef_fst,
      clear_except bef_fst,
      dsimp at bef_fst,
      rw option.some_inj at bef_fst,
      exact bef_fst,
    },
    clear_except rin nt_match,

    repeat {
      rw list.mem_append at rin,
    },
    cases rin,
    {
      cases rin,
      {
        rw list.mem_map at rin,
        rcases rin with ⟨r₀, hr₀g₁, wrap_eq_r⟩,
        rw ←wrap_eq_r at nt_match,
        unfold wrap_grule₁ at nt_match,
        have inl_match := symbol.nonterminal.inj nt_match,
        change sum.inl none = sum.inl (some (sum.inl r₀.input_N)) at inl_match,
        have none_eq_some := sum.inl.inj inl_match,
        clear_except none_eq_some,
        tauto,
      },
      {
        rw list.mem_map at rin,
        rcases rin with ⟨r₀, hr₀g₂, wrap_eq_r⟩,
        rw ←wrap_eq_r at nt_match,
        unfold wrap_grule₂ at nt_match,
        have inl_match := symbol.nonterminal.inj nt_match,
        change sum.inl none = sum.inl (some (sum.inr r₀.input_N)) at inl_match,
        have none_eq_some := sum.inl.inj inl_match,
        clear_except none_eq_some,
        tauto,
      },
    },
    {
      cases rin,
      {
        unfold rules_for_terminals₁ at rin,
        rw list.mem_map at rin,
        rcases rin with ⟨t, htg₁, tt_eq_r⟩,
        rw ←tt_eq_r at nt_match,
        have inl_eq_inr := symbol.nonterminal.inj nt_match,
        change sum.inl none = sum.inr (sum.inl t) at inl_eq_inr,
        clear_except inl_eq_inr,
        tauto,
      },
      {
        unfold rules_for_terminals₂ at rin,
        rw list.mem_map at rin,
        rcases rin with ⟨t, htg₂, tt_eq_r⟩,
        rw ←tt_eq_r at nt_match,
        have inl_eq_inr := symbol.nonterminal.inj nt_match,
        change sum.inl none = sum.inr (sum.inr t) at inl_eq_inr,
        clear_except inl_eq_inr,
        tauto,
      },
    },
  },
  clear hyp_tran,
  rw w₁eq at hyp_deri,

  have hope_result := big_induction hyp_deri,
  clear_except hope_result,
  rcases hope_result with ⟨x, y, ⟨deri_x, deri_y⟩, concat_xy⟩,

  use list.take x.length w,
  use list.drop x.length w,
  split,
  {
    clear deri_y,
    unfold grammar_language,
    rw set.mem_set_of_eq,
    unfold grammar_generates,
    convert deri_x,
    clear deri_x,

    have xylen := corresponding_strings_length concat_xy,
    rw list.length_append at xylen,
    repeat {
      rw list.length_map at xylen,
    },

    ext1 i,
    by_cases i ≥ x.length,
    {
      convert_to none = none,
      {
        have xlen : x.length = (list.map (@symbol.terminal T g₁.nt) (list.take x.length w)).length,
        {
          clear_except xylen,
          rw list.length_map,
          rw list.length_take,
          symmetry,
          apply min_eq_left,
          exact nat.le.intro xylen,
        },
        rw xlen at h,
        clear_except h,
        rw list.nth_eq_none_iff,
        exact h,
      },
      {
        clear_except h,
        rw list.nth_eq_none_iff,
        exact h,
      },
      refl,
    },
    push_neg at h,
    rename h i_lt_len_x,

    have i_lt_len_lwx : i < (list.map (wrap_symbol₁ g₂.nt) x).length,
    {
      rw list.length_map,
      exact i_lt_len_x,
    },
    have i_lt_len_w : i < w.length,
    {
      apply lt_of_lt_of_le i_lt_len_x,
      exact nat.le.intro xylen,
    },
    have i_lt_len₁ : i < (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y).length,
    {
      rw list.length_append,
      apply lt_of_lt_of_le i_lt_len_lwx,
      apply le_self_add,
    },
    have i_lt_len₂ : i < (list.map symbol.terminal w).length,
    {
      rw list.length_map,
      exact i_lt_len_w,
    },
    rw list.nth_map,
    rw list.nth_take i_lt_len_x,

    have equivalent_ith :
      corresponding_symbols
        (list.nth_le (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) i i_lt_len₁)
        (list.nth_le (list.map symbol.terminal w) i i_lt_len₂),
    {
      apply corresponding_strings_nth_le,
      exact concat_xy,
    },
    rw list.nth_le_map at equivalent_ith, swap,
    {
      exact i_lt_len_w,
    },
    rw list.nth_le_append at equivalent_ith, swap,
    {
      exact i_lt_len_lwx,
    },
    rw list.nth_le_map at equivalent_ith, swap,
    {
      exact i_lt_len_x,
    },
    clear_except equivalent_ith,
    rw list.nth_le_nth i_lt_len_x,
    cases x.nth_le i i_lt_len_x with t n;
    unfold wrap_symbol₁ at equivalent_ith;
    unfold corresponding_symbols at equivalent_ith,
    {
      have symbol_ith := congr_arg (@symbol.terminal T g₁.nt) equivalent_ith,
      rw list.nth_le_nth i_lt_len_w,
      rw option.map_some',
      exact congr_arg option.some symbol_ith,
    },
    {
      exfalso,
      exact equivalent_ith,
    },
  },
  split,
  {
    clear deri_x,
    unfold grammar_language,
    rw set.mem_set_of_eq,
    unfold grammar_generates,
    convert deri_y,
    clear deri_y,

    have xylen := corresponding_strings_length concat_xy,
    rw list.length_append at xylen,
    repeat {
      rw list.length_map at xylen,
    },

    ext1 i,
    by_cases i ≥ y.length,
    {
      convert_to none = none,
      {
        have ylen : y.length = (list.map (@symbol.terminal T g₁.nt) (list.drop x.length w)).length,
        {
          clear_except xylen,
          rw list.length_map,
          rw list.length_drop,
          omega,
        },
        rw ylen at h,
        clear_except h,
        rw list.nth_eq_none_iff,
        rw list.length_map at *,
        exact h,
      },
      {
        clear_except h,
        rw list.nth_eq_none_iff,
        exact h,
      },
      refl,
    },
    push_neg at h,
    rename h i_lt_len_y,

    rw ←list.take_append_drop (list.map (wrap_symbol₁ g₂.nt) x).length (list.map symbol.terminal w) at concat_xy,
    rw list.nth_map,

    have equivalent_second_parts :
      corresponding_strings
        (list.map (wrap_symbol₂ g₁.nt) y)
        (list.drop (list.map (wrap_symbol₁ g₂.nt) x).length (list.map symbol.terminal w)),
    {
      have llen_eq_llen :
        (list.map (wrap_symbol₁ g₂.nt) x).length =
        (list.take (list.map (wrap_symbol₁ g₂.nt) x).length (list.map symbol.terminal w)).length,
      {
        rw list.length_take,
        symmetry,
        apply min_eq_left,
        rw list.length_map,
        rw list.length_map,
        exact nat.le.intro xylen,
      },
      convert corresponding_strings_drop (list.map (wrap_symbol₁ g₂.nt) x).length concat_xy,
      {
        rw list.drop_left,
      },
      {
        rw list.take_append_drop,
      },
      exact T,
    },
    clear concat_xy,
    symmetry,

    have i_lt_len_lwy : i < (list.map (wrap_symbol₂ g₁.nt) y).length,
    {
      rw list.length_map,
      exact i_lt_len_y,
    },
    have i_lt_len_dxw : i < (list.drop x.length (list.map symbol.terminal w)).length,
    {
      rw list.length_drop,
      rw list.length_map,
      rw ←xylen,
      convert i_lt_len_lwy,
      rw list.length_map,
      rw add_comm,
      rw nat.add_sub_assoc,
      rw nat.sub_self,
      rw nat.add_zero,
      refl,
    },
    have i_lt_len_mtw : i < (list.map symbol.terminal (list.drop x.length w)).length,
    {
      convert i_lt_len_dxw,
      apply list.map_drop,
    },
    have i_lt_len_dlmxw :
      i < (list.drop (list.map (wrap_symbol₁ g₂.nt) x).length (list.map symbol.terminal w)).length,
    {
      rw list.length_map,
      -- DO NOT call `i_lt_len_dxw` even though it looks like a good idea!
      rw list.length_drop,
      rw list.length_map,
      rw ←xylen,
      convert i_lt_len_lwy,
      rw list.length_map,
      rw add_comm,
      rw nat.add_sub_assoc,
      rw nat.sub_self,
      rw nat.add_zero,
      refl,
    },
    have eqiv_symb := corresponding_strings_nth_le i_lt_len_lwy i_lt_len_dlmxw equivalent_second_parts,

    have goal_as_ith_drop :
      y.nth_le i i_lt_len_y = (list.drop x.length (list.map symbol.terminal w)).nth_le i i_lt_len_dxw,
    {
      have xli_lt_len_w : x.length + i < w.length,
      {
        clear_except i_lt_len_y xylen,
        linarith,
      },
      rw list.nth_le_map _ _ i_lt_len_y at eqiv_symb,
      rw list.nth_le_drop' at *,
      rw list.nth_le_map, swap,
      {
        exact xli_lt_len_w,
      },
      rw list.nth_le_map at eqiv_symb, swap,
      {
        rw list.length_map,
        exact xli_lt_len_w,
      },
      clear_except eqiv_symb,

      cases y.nth_le i i_lt_len_y with t n,
      {
        unfold wrap_symbol₂ at eqiv_symb,
        unfold corresponding_symbols at eqiv_symb,
        have eq_symb := congr_arg symbol.terminal eqiv_symb,
        rw ←eq_symb,
        apply congr_arg symbol.terminal,
        simp only [list.length_map],
      },
      {
        exfalso,
        unfold wrap_symbol₂ at eqiv_symb,
        unfold corresponding_symbols at eqiv_symb,
        exact eqiv_symb,
      },
    },
    have goal_as_some_ith :
      some (y.nth_le i i_lt_len_y) =
      some ((list.map symbol.terminal (list.drop x.length w)).nth_le i i_lt_len_mtw),
    {
      rw goal_as_ith_drop,
      clear_except,
      congr,
      rw list.map_drop,
    },
    clear_except goal_as_some_ith,
    rw ←list.nth_le_nth i_lt_len_y at goal_as_some_ith,
    rw ←list.nth_le_nth i_lt_len_mtw at goal_as_some_ith,
    convert goal_as_some_ith,
    rw list.nth_map,
  },
  apply list.take_append_drop,
end

end very_complicated

end hard_direction


/-- The class of recursively-enumerable languages is closed under concatenation. -/
theorem RE_of_RE_c_RE (L₁ : language T) (L₂ : language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ * L₂)   :=
begin
  rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩,

  use big_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    -- prove `L₁ * L₂ ⊇` here
    intros w hyp,
    rw ←h₁,
    rw ←h₂,
    exact in_concatenated_of_in_big hyp,
  },
  {
    -- prove `L₁ * L₂ ⊆` here
    intros w hyp,
    rw ←h₁ at hyp,
    rw ←h₂ at hyp,
    exact in_big_of_in_concatenated hyp,
  },
end
