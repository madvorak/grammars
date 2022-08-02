import unrestricted.grammar


variables {T : Type}

def as_terminal {N : Type} : symbol T N → option T
| (symbol.terminal t)    := some t
| (symbol.nonterminal _) := none

def all_used_terminals (g : grammar T) : list T :=
list.filter_map as_terminal (list.join (list.map grule.output_string g.rules))


-- new nonterminal type
private def nnn (N₁ N₂ : Type) : Type :=
option (N₁ ⊕ N₂) ⊕ (T ⊕ T)

-- new symbol type
private def nst (T : Type) (N₁ N₂ : Type) : Type :=
symbol T (@nnn T N₁ N₂)

private def wrap_symbol₁ {N₁ : Type} (N₂ : Type) : symbol T N₁ → nst T N₁ N₂
| (symbol.terminal t)    := symbol.nonterminal (sum.inr (sum.inl t))
| (symbol.nonterminal n) := symbol.nonterminal (sum.inl (some (sum.inl n)))

private def wrap_symbol₂ {N₂ : Type} (N₁ : Type) : symbol T N₂ → nst T N₁ N₂
| (symbol.terminal t)    := symbol.nonterminal (sum.inr (sum.inr t))
| (symbol.nonterminal n) := symbol.nonterminal (sum.inl (some (sum.inr n)))

private def wrap_grule₁ {N₁ : Type} (N₂ : Type) (r : grule T N₁) : grule T (nnn N₁ N₂) :=
grule.mk (
    list.map (wrap_symbol₁ N₂) r.input_string.first,
    sum.inl (some (sum.inl r.input_string.secon)),
    list.map (wrap_symbol₁ N₂) r.input_string.third)
  (list.map (wrap_symbol₁ N₂) r.output_string)

private def wrap_grule₂ {N₂ : Type} (N₁ : Type) (r : grule T N₂) : grule T (nnn N₁ N₂) :=
grule.mk (
    list.map (wrap_symbol₂ N₁) r.input_string.first,
    sum.inl (some (sum.inr r.input_string.secon)),
    list.map (wrap_symbol₂ N₁) r.input_string.third)
  (list.map (wrap_symbol₂ N₁) r.output_string)

private def rules_for_terminals₁ (N₂ : Type) (g : grammar T) : list (grule T (nnn g.nt N₂)) :=
list.map (λ t, grule.mk ([], sum.inr (sum.inl t), []) [symbol.terminal t]) (all_used_terminals g)

private def rules_for_terminals₂ (N₁ : Type) (g : grammar T) : list (grule T (nnn N₁ g.nt)) :=
list.map (λ t, grule.mk ([], sum.inr (sum.inr t), []) [symbol.terminal t]) (all_used_terminals g)

-- the grammar for concatenation of `g₁` and `g₂` languages
private def big_grammar (g₁ g₂ : grammar T) : grammar T :=
grammar.mk
  (nnn g₁.nt g₂.nt)
  (sum.inl none)
  ((grule.mk ([], sum.inl none, []) [
    symbol.nonterminal (sum.inl (some (sum.inl g₁.initial))),
    symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]
  ) :: (
    (list.map (wrap_grule₁ g₂.nt) g₁.rules ++ list.map (wrap_grule₂ g₁.nt) g₂.rules) ++
    (rules_for_terminals₁ g₂.nt g₁ ++ rules_for_terminals₂ g₁.nt g₂)
  ))


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
    {g : grammar T} {w : list (symbol T g.nt)}
    (ass : grammar_derives g [symbol.nonterminal g.initial] w)
    {s : symbol T g.nt} (symbol_derived : s ∈ w) :
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

private lemma substitute_terminals {g₁ g₂ : grammar T} {side : T → T ⊕ T} {w : list T}
    (rule_for_each_terminal : ∀ t ∈ w,
      (grule.mk ([], sum.inr (side t), []) [symbol.terminal t]) ∈
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
  rw list.append_singleton_of_cons,
  rw list.append_singleton_of_cons (symbol.terminal d),
  have step_head :
    grammar_transforms (big_grammar g₁ g₂)
      ([(symbol.nonterminal ∘ sum.inr ∘ side) d] ++ list.map (symbol.nonterminal ∘ sum.inr ∘ side) l)
      ([symbol.terminal d] ++ list.map (symbol.nonterminal ∘ sum.inr ∘ side) l),
  {
    use grule.mk ([], sum.inr (side d), []) [symbol.terminal d],
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
  apply grammar_derives_with_prefix,
  apply ih,
  {
    intros t tin,
    apply rule_for_each_terminal t,
    exact list.mem_cons_of_mem d tin,
  },
end

private lemma in_big_of_in_concatenated
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

  rw ← hw,
  rw list.map_append,

  apply @grammar_deri_of_deri_deri T (big_grammar g₁ g₂) _
    (list.map symbol.terminal u ++ [symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]) _,
  {
    clear_except hu,
    rw list.two_singletons_of_doubleton,
    apply grammar_derives_with_postfix,
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
    apply grammar_derives_with_prefix,
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

private def equivalent_symbols {N₁ N₂ : Type} : nst T N₁ N₂ → nst T N₁ N₂ → Prop
| (symbol.terminal t)                               (symbol.terminal t')                               := t = t'
| (symbol.nonterminal (sum.inr (sum.inl a)))        (symbol.nonterminal (sum.inr (sum.inl a')))        := a = a'
| (symbol.nonterminal (sum.inr (sum.inl a)))        (symbol.nonterminal (sum.inr (sum.inr a')))        := a = a'
| (symbol.nonterminal (sum.inr (sum.inr a)))        (symbol.nonterminal (sum.inr (sum.inl a')))        := a = a'
| (symbol.nonterminal (sum.inr (sum.inr a)))        (symbol.nonterminal (sum.inr (sum.inr a')))        := a = a'
| (symbol.terminal t)                               (symbol.nonterminal (sum.inr (sum.inl a)))         := t = a
| (symbol.nonterminal (sum.inr (sum.inl a)))        (symbol.terminal t)                                := t = a
| (symbol.terminal t)                               (symbol.nonterminal (sum.inr (sum.inr a)))         := t = a
| (symbol.nonterminal (sum.inr (sum.inr a)))        (symbol.terminal t)                                := t = a
| (symbol.nonterminal (sum.inl (some (sum.inl n)))) (symbol.nonterminal (sum.inl (some (sum.inl n')))) := n = n'
| (symbol.nonterminal (sum.inl (some (sum.inr n)))) (symbol.nonterminal (sum.inl (some (sum.inr n')))) := n = n'
| (symbol.nonterminal (sum.inl (none)))             (symbol.nonterminal (sum.inl (none)))              := true
| _                                                 _                                                  := false

private lemma equivalent_symbols_reflexive {N₁ N₂ : Type} : reflexive (@equivalent_symbols T N₁ N₂) :=
begin
  intro x,
  repeat {
    try {
      cases x,
    },
    try {
      unfold equivalent_symbols,
    },
  },
end

private lemma equivalent_symbols_symmetric {N₁ N₂ : Type} : symmetric (@equivalent_symbols T N₁ N₂) :=
begin
  intros x y hxy,
  sorry,
end

private lemma equivalent_symbols_transitive {N₁ N₂ : Type} : transitive (@equivalent_symbols T N₁ N₂) :=
begin
  intros x y z hxy hyz,
  sorry,
end

private def equivalent_strings {N₁ N₂ : Type} : list (nst T N₁ N₂) → list (nst T N₁ N₂) → Prop :=
list.forall₂ equivalent_symbols

private lemma equivalent_strings_refl {N₁ N₂ : Type} {x : list (nst T N₁ N₂)} :
  equivalent_strings x x :=
begin
  apply list.forall₂_same,
  intros x xin,
  apply equivalent_symbols_reflexive,
end

private lemma equivalent_strings_trans {N₁ N₂ : Type} {x y z : list (nst T N₁ N₂)}
    (hxy : equivalent_strings x y)
    (hyz : equivalent_strings y z) :
  equivalent_strings x z :=
begin
  sorry,
end

private lemma equivalent_strings_append {N₁ N₂ : Type} {x₁ x₂ y₁ y₂ : list (nst T N₁ N₂)}
    (ass₁ : equivalent_strings x₁ y₁)
    (ass₂ : equivalent_strings x₂ y₂) :
  equivalent_strings (x₁ ++ x₂) (y₁ ++ y₂) :=
begin
  unfold equivalent_strings at *,
  sorry,
end

private lemma equivalent_strings_length {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (ass : equivalent_strings x y) :
  x.length = y.length :=
begin
  unfold equivalent_strings at ass,
  exact list.forall₂_length_eq ass,
end

private lemma equivalent_strings_nth_le {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    {i : ℕ} (i_lt_len_x : i < x.length) (i_lt_len_y : i < y.length) -- one of them should follow from the other
    (ass : equivalent_strings x y) :
  equivalent_symbols (x.nth_le i i_lt_len_x) (y.nth_le i i_lt_len_y) :=
begin
  unfold equivalent_strings at *,
  sorry,
end

private lemma equivalent_strings_reverse {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (ass : equivalent_strings x y) :
  equivalent_strings x.reverse y.reverse :=
begin
  unfold equivalent_strings at *,
  rw list.forall₂_reverse_iff,
  exact ass,
end

private lemma equivalent_strings_of_reverse {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (ass : equivalent_strings x.reverse y.reverse) :
  equivalent_strings x y :=
begin
  unfold equivalent_strings at *,
  rw list.forall₂_reverse_iff at ass,
  exact ass,
end

private lemma equivalent_strings_take {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    (n : ℕ) (ass : equivalent_strings x y) :
  equivalent_strings (list.take n x) (list.take n y) :=
begin
  unfold equivalent_strings at *,
  exact list.forall₂_take n ass,
end


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

private lemma unwrap_wrap₁ {N₁ N₂ : Type} : unwrap_symbol₁ ∘ @wrap_symbol₁ T N₁ N₂ = option.some :=
begin
  ext1 a,
  cases a;
  refl,
end

private lemma unwrap_wrap₂ {N₁ N₂ : Type} : unwrap_symbol₂ ∘ @wrap_symbol₂ T N₁ N₂ = option.some :=
begin
  ext1 a,
  cases a;
  refl,
end


private lemma big_induction {g₁ g₂ : grammar T} {w : list (symbol T (nnn g₁.nt g₂.nt))} (ass :
    grammar_derives (big_grammar g₁ g₂)
      [symbol.nonterminal (sum.inl (some (sum.inl g₁.initial))),
       symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]
      w
    ) :
  ∃ x : list (symbol T g₁.nt),
  ∃ y : list (symbol T g₂.nt),
    and
      (and
        (grammar_derives g₁ [symbol.nonterminal g₁.initial] x)
        (grammar_derives g₂ [symbol.nonterminal g₂.initial] y)
      )
      (equivalent_strings (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) w) :=
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
      rw ← list.two_singletons_of_doubleton,
      unfold equivalent_strings,
      rw list.forall₂_cons,
      split,
      {
        unfold equivalent_symbols,
      },
      rw list.forall₂_cons,
      split,
      {
        unfold equivalent_symbols,
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
    simp only [prod.first, prod.secon, prod.third, list.append_nil] at bef,
    rw bef at ih_concat,
    have same_lengths := equivalent_strings_length ih_concat,
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
    have eqi_symb := equivalent_strings_nth_le ulen₁ ulen₂ ih_concat,
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
      rw list.mem_map at rin,
      rcases rin with ⟨r₁, rin₁, wrap_r₁_eq_r⟩,
      rw ← wrap_r₁_eq_r at *,
      clear wrap_r₁_eq_r,
      simp [wrap_grule₁, prod.first, prod.secon, prod.third] at *,
      rw ← list.singleton_append at bef,

      let m := (list.map (wrap_symbol₁ g₂.nt) r₁.input_string.first).length + 1 +
               (list.map (wrap_symbol₁ g₂.nt) r₁.input_string.third).length,
      let a' := u ++ list.map (wrap_symbol₁ g₂.nt) r₁.output_string ++ list.take (x.length - u.length - m) v,
      use list.filter_map unwrap_symbol₁ a',
      use y,

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
              equivalent_strings
                (list.map (wrap_symbol₁ g₂.nt) x)
                (list.take x.length (u
                  ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_string.first
                  ++ [symbol.nonterminal (sum.inl (some (sum.inl r₁.input_string.secon)))]
                  ++ list.map (wrap_symbol₁ g₂.nt) r₁.input_string.third
                  ++ v)),
            {
              rw bef at ih_concat,
              clear_except ih_concat,
              rw ← list.append_assoc _ _ v at ih_concat,
              rw ← list.append_assoc _ _ v at ih_concat,
              rw list.append_assoc u,
              rw list.append_assoc u,
              rw list.append_assoc u,
              rw list.append_assoc (list.map (wrap_symbol₁ g₂.nt) r₁.input_string.first),
              unfold equivalent_strings at *,

              convert list.forall₂_take x.length ih_concat,
              {
                have x_len_eq : x.length = (list.map (wrap_symbol₁ g₂.nt) x).length,
                {
                  rw list.length_map,
                },
                rw x_len_eq,
                rw list.take_left,
              },
            },
            sorry,
          },
          {
            rw list.filter_map_append_append,
            congr,
            rw list.filter_map_map,
            rw unwrap_wrap₁,
            apply list.filter_map_some,
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

      apply equivalent_strings_append,
      {
        have wrap_unwrap_u : list.map (wrap_symbol₁ g₂.nt) (list.filter_map unwrap_symbol₁ u) = u,
        {
          -- express `u` as a fragment of `x` probably
          sorry,
        },
        rw wrap_unwrap_u,
        apply equivalent_strings_refl,
      },
      apply equivalent_strings_append,
      {
        rw list.filter_map_map,
        rw unwrap_wrap₁,
        rw list.filter_map_some,
        apply equivalent_strings_refl,
      },
      convert_to equivalent_strings _ (list.take (x.length - u.length - m) v ++ list.drop (x.length - u.length - m) v),
      {
        rw list.take_append_drop,
      },
      apply equivalent_strings_append,
      {
        have wrap_unwrap_v :
          list.map (wrap_symbol₁ g₂.nt) (list.filter_map unwrap_symbol₁ (
              list.take (x.length - u.length - m) v)
            ) =
          list.take (x.length - u.length - m) v,
        {
          -- the prefix of `v` should probably be expressed as a fragment of `x` too
          sorry,
        },
        rw wrap_unwrap_v,
        apply equivalent_strings_refl,
      },
      -- now we have what `g₂` generated
      have reverse_concat := equivalent_strings_reverse ih_concat,
      repeat { rw list.reverse_append at reverse_concat },
      have the_part := equivalent_strings_take y.length reverse_concat,
      apply equivalent_strings_of_reverse,

      have len_sum : y.length + (x.length - u.length - m) = v.length,
      {
        change
          y.length + (x.length - u.length - (
            (list.map (wrap_symbol₁ g₂.nt) r₁.input_string.first).length + 1 +
            (list.map (wrap_symbol₁ g₂.nt) r₁.input_string.third).length
          )) =
          v.length,
        have len_concat := equivalent_strings_length ih_concat,
        clear_except len_concat,
        repeat { rw list.length_append at len_concat },
        rw list.length_map at len_concat,
        rw list.length_map at len_concat,
        rw list.length_singleton at len_concat,
        rw [prod.first, prod.third],
        rw ← nat.add_sub_assoc,
        swap, sorry, -- TODO
        rw ← nat.add_sub_assoc,
        swap, sorry,
        rw add_comm at len_concat,
        rw len_concat,
        clear len_concat,
        rw add_tsub_cancel_left,
        rw ← nat.add_assoc,
        rw ← nat.add_assoc,
        rw add_tsub_cancel_left,
      },
      have yl_lt_vl : y.length ≤ v.length,
      {
        exact nat.le.intro len_sum,
      },
      convert_to equivalent_strings _ (list.take y.length v.reverse),
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
      rw list.take_append_of_le_length at the_part,
      swap, {
        rw list.length_reverse,
        rw list.length_map,
      },
      repeat { rw list.append_assoc at the_part },
      rw list.take_append_of_le_length at the_part,
      swap, {
        rw list.length_reverse,
        exact yl_lt_vl,
      },
      rw list.take_all_of_le at the_part,
      swap, {
        rw list.length_reverse,
        rw list.length_map,
      },
      exact the_part,
    },
    {
      use x,
      -- prove this part only after everything else is finished and polished
      sorry,
    },
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
      rw ← eq_r at *,
      clear eq_r,
      dsimp [prod.first, prod.secon, prod.third] at *,
      rw list.append_nil at ih_concat,
      rw list.append_nil at ih_concat,
      have equiv_utv :
        equivalent_strings
          (u ++ [symbol.nonterminal (sum.inr (sum.inl t))] ++ v)
          (u ++ [symbol.terminal t] ++ v),
      {
        apply equivalent_strings_append,
        apply equivalent_strings_append,
        apply equivalent_strings_refl,
        {
          unfold equivalent_strings,
          rw list.forall₂_cons,
          unfold equivalent_symbols,
          exact ⟨rfl, list.forall₂.nil⟩,
        },
        apply equivalent_strings_refl,
      },
      exact equivalent_strings_trans ih_concat equiv_utv,
    },
    {
      unfold rules_for_terminals₂ at rin,
      rw list.mem_map at rin,
      rcases rin with ⟨t, -, eq_r⟩,
      rw ← eq_r at *,
      clear eq_r,
      dsimp [prod.first, prod.secon, prod.third] at *,
      rw list.append_nil at ih_concat,
      rw list.append_nil at ih_concat,
      have equiv_utv :
        equivalent_strings
          (u ++ [symbol.nonterminal (sum.inr (sum.inr t))] ++ v)
          (u ++ [symbol.terminal t] ++ v),
      {
        apply equivalent_strings_append,
        apply equivalent_strings_append,
        apply equivalent_strings_refl,
        {
          unfold equivalent_strings,
          rw list.forall₂_cons,
          unfold equivalent_symbols,
          exact ⟨rfl, list.forall₂.nil⟩,
        },
        apply equivalent_strings_refl,
      },
      exact equivalent_strings_trans ih_concat equiv_utv,
    },
  },
end

private lemma in_concatenated_of_in_big
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
    have rif_nil : r.input_string.first = [], swap,
    any_goals {
      clear_except bef_len,
      rw ← list.length_eq_zero,
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
    have nt_match : symbol.nonterminal (big_grammar g₁ g₂).initial = symbol.nonterminal r.input_string.secon,
    {
      have bef_fst := congr_fun (congr_arg list.nth bef) 0,
      rw [u_nil, rif_nil] at bef_fst,
      clear_except bef_fst,
      dsimp at bef_fst,
      rw option.some_inj at bef_fst,
      exact bef_fst,
    },
    clear_except rin nt_match,

    repeat { rw list.mem_append at rin },
    cases rin,
    {
      cases rin,
      {
        rw list.mem_map at rin,
        rcases rin with ⟨r₀, hr₀g₁, wrap_eq_r⟩,
        rw ← wrap_eq_r at nt_match,
        unfold wrap_grule₁ at nt_match,
        dsimp [prod.secon] at nt_match,
        have inl_match := symbol.nonterminal.inj nt_match,
        change sum.inl none = sum.inl (some (sum.inl r₀.input_string.secon)) at inl_match,
        have none_eq_some := sum.inl.inj inl_match,
        clear_except none_eq_some,
        tauto,
      },
      {
        rw list.mem_map at rin,
        rcases rin with ⟨r₀, hr₀g₂, wrap_eq_r⟩,
        rw ← wrap_eq_r at nt_match,
        unfold wrap_grule₂ at nt_match,
        dsimp [prod.secon] at nt_match,
        have inl_match := symbol.nonterminal.inj nt_match,
        change sum.inl none = sum.inl (some (sum.inr r₀.input_string.secon)) at inl_match,
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
        rw ← tt_eq_r at nt_match,
        dsimp [prod.secon] at nt_match,
        have inl_eq_inr := symbol.nonterminal.inj nt_match,
        change sum.inl none = sum.inr (sum.inl t) at inl_eq_inr,
        clear_except inl_eq_inr,
        tauto,
      },
      {
        unfold rules_for_terminals₂ at rin,
        rw list.mem_map at rin,
        rcases rin with ⟨t, htg₂, tt_eq_r⟩,
        rw ← tt_eq_r at nt_match,
        dsimp [prod.secon] at nt_match,
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

    have xylen := equivalent_strings_length concat_xy,
    rw list.length_append at xylen,
    repeat { rw list.length_map at xylen },

    ext1 i,
    by_cases i ≥ x.length,
    {
      convert_to none = none,
      {
        have xlens : x.length = (list.map (@symbol.terminal T g₁.nt) (list.take x.length w)).length,
        {
          clear_except xylen,
          rw list.length_map,
          rw list.length_take,
          symmetry,
          apply min_eq_left,
          exact nat.le.intro xylen,
        },
        rw xlens at h,
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
      equivalent_symbols
        (list.nth_le (list.map (wrap_symbol₁ g₂.nt) x ++ list.map (wrap_symbol₂ g₁.nt) y) i i_lt_len₁)
        (list.nth_le (list.map symbol.terminal w) i i_lt_len₂),
    {
      apply equivalent_strings_nth_le,
      exact concat_xy,
    },
    rw list.nth_le_map at equivalent_ith,
    swap, {
      exact i_lt_len_w,
    },
    rw list.nth_le_append at equivalent_ith,
    swap, {
      exact i_lt_len_lwx,
    },
    rw list.nth_le_map at equivalent_ith,
    swap, {
      exact i_lt_len_x,
    },
    clear_except equivalent_ith,
    rw list.nth_le_nth i_lt_len_x,
    cases x.nth_le i i_lt_len_x with t n;
    unfold wrap_symbol₁ at equivalent_ith;
    unfold equivalent_symbols at equivalent_ith,
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

    have xylen := equivalent_strings_length concat_xy,
    rw list.length_append at xylen,
    repeat { rw list.length_map at xylen },

    ext1 i,
    by_cases i ≥ y.length,
    {
      convert_to none = none,
      {
        have ylens : y.length = (list.map (@symbol.terminal T g₁.nt) (list.drop x.length w)).length,
        {
          clear_except xylen,
          rw list.length_map,
          rw list.length_drop,
          omega,
        },
        rw ylens at h,
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

    rw ← list.take_append_drop (list.map (wrap_symbol₁ g₂.nt) x).length (list.map symbol.terminal w) at concat_xy,
    rw list.nth_map,

    have equivalent_second_parts :
      equivalent_strings
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
      swap, {
        exact T,
      },
      unfold equivalent_strings at concat_xy ⊢,
      convert list.forall₂_drop (list.map (wrap_symbol₁ g₂.nt) x).length concat_xy,
      {
        rw list.drop_left,
      },
      {
        rw list.take_append_drop,
      },
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
      rw ← xylen,
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
      rw ← xylen,
      convert i_lt_len_lwy,
      rw list.length_map,
      rw add_comm,
      rw nat.add_sub_assoc,
      rw nat.sub_self,
      rw nat.add_zero,
      refl,
    },
    have eqiv_symb := equivalent_strings_nth_le i_lt_len_lwy i_lt_len_dlmxw equivalent_second_parts,

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
      rw list.nth_le_map at *,
      swap, {
        exact xli_lt_len_w,
      },
      swap, {
        rw list.length_map,
        exact xli_lt_len_w,
      },
      clear_except eqiv_symb,

      cases y.nth_le i i_lt_len_y with t n,
      {
        unfold wrap_symbol₂ at eqiv_symb,
        unfold equivalent_symbols at eqiv_symb,
        have eq_symb := congr_arg symbol.terminal eqiv_symb,
        rw ← eq_symb,
        apply congr_arg symbol.terminal,
        simp only [list.length_map],
      },
      {
        exfalso,
        unfold wrap_symbol₂ at eqiv_symb,
        unfold equivalent_symbols at eqiv_symb,
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
    rw ← list.nth_le_nth i_lt_len_y at goal_as_some_ith,
    rw ← list.nth_le_nth i_lt_len_mtw at goal_as_some_ith,
    convert goal_as_some_ith,
    rw list.nth_map,
  },
  apply list.take_append_drop,
end

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
    rw ← h₁,
    rw ← h₂,
    exact in_concatenated_of_in_big hyp,
  },
  {
    -- prove `L₁ * L₂ ⊆` here
    intros w hyp,
    rw ← h₁ at hyp,
    rw ← h₂ at hyp,
    exact in_big_of_in_concatenated hyp,
  },
end
