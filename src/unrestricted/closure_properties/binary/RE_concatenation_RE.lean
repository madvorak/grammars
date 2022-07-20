import unrestricted.grammar


variables {T : Type} [decidable_eq T]

def as_terminal {N : Type} : symbol T N → option T
| (symbol.terminal t)    := some t
| (symbol.nonterminal _) := none

def all_used_terminals (g : grammar T) : list T :=
list.dedup (list.filter_map as_terminal (
  list.join (list.map grule.output_string g.rules)))


-- new nonterminal type
private def nnn (N₁ N₂ : Type) : Type :=
option (N₁ ⊕ N₂) ⊕ (T ⊕ T)

-- new symbol type
private def nst (T : Type) [decidable_eq T] (N₁ N₂ : Type) : Type :=
symbol T (@nnn T _ N₁ N₂)

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


section todo_move

lemma two_singletons_of_doubleton {α : Type} {a b : α} : [a, b] = [a] ++ [b] :=
rfl

lemma append_of_quadrupledot {α : Type} (a : α) (l : list α) : a :: l = [a] ++ l :=
rfl

end todo_move


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
  rcases orig with ⟨ r, rin, u, v, bef, aft ⟩,
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
  rw append_of_quadrupledot,
  rw append_of_quadrupledot (symbol.terminal d),
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
  rcases ass with ⟨ u, v, hu, hv, hw ⟩,
  unfold grammar_language at *,
  rw set.mem_set_of_eq at *,
  unfold grammar_generates at *,
  apply grammar_deri_of_tran_deri first_transformation,

  rw ← hw,
  rw list.map_append,

  apply @grammar_deri_of_deri_deri T _ (big_grammar g₁ g₂) _
    (list.map symbol.terminal u ++ [symbol.nonterminal (sum.inl (some (sum.inr g₂.initial)))]) _,
  {
    clear_except hu,
    rw two_singletons_of_doubleton,
    apply grammar_derives_with_postfix,
    apply @grammar_deri_of_deri_deri _ _ _ _ (list.map (
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
        rcases orig with ⟨ r, rin, u, v, bef, aft ⟩,
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
          rw list.mem_dedup,
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
    apply @grammar_deri_of_deri_deri _ _ _ _ (list.map (
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
        rcases orig with ⟨ r, rin, u, v, bef, aft ⟩,
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
          rw list.mem_dedup,
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

private lemma equivalent_symbols_reflexive {N₁ N₂ : Type} : reflexive (@equivalent_symbols T _ N₁ N₂) :=
begin
  intro x,
  cases x,
  unfold equivalent_symbols,
  cases x,
  cases x,
  unfold equivalent_symbols,
  cases x,
  unfold equivalent_symbols,
  unfold equivalent_symbols,
  cases x,
  unfold equivalent_symbols,
  unfold equivalent_symbols,
end

private lemma equivalent_symbols_symmetric {N₁ N₂ : Type} : symmetric (@equivalent_symbols T _ N₁ N₂) :=
begin
  intros x y hxy,
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
list.forall₂_length_eq ass


private lemma equivalent_strings_nth_le {N₁ N₂ : Type} {x y : list (nst T N₁ N₂)}
    {i : ℕ} (i_lt_len_x : i < x.length) (i_lt_len_y : i < y.length) -- one of them should follow from the other
    (ass : equivalent_strings x y) :
  equivalent_symbols (x.nth_le i i_lt_len_x) (y.nth_le i i_lt_len_y) :=
begin
  unfold equivalent_strings at *,
  sorry,
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
      rw ← two_singletons_of_doubleton,
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
    sorry,
  },
  rw list.mem_append at rin,
  cases rin,
  {
    rw list.mem_append at rin,
    cases rin,
    {
      sorry,
    },
    {
      sorry,
    },
  },
  {
    rw list.mem_append at rin,
    cases rin,
    {
      unfold rules_for_terminals₁ at rin,
      rw list.mem_map at rin,
      rcases rin with ⟨t, -, eq_r⟩,
      rw ← eq_r at *,
      clear eq_r,
      dsimp [prod.first, prod.secon, prod.third] at *,
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
      sorry,
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
    change _ ∈ list.cons _ _ at rin,
    rw list.mem_cons_iff at rin,
    cases rin,
    {
      rw rin at bef aft,
      dsimp at bef aft,
      have bef_len := congr_arg list.length bef,
      rw list.length_append_append at bef_len,
      rw list.length_append_append at bef_len,
      dsimp at bef_len,
      have u_nil : u = [], swap,
      have v_nil : v = [], swap,
      rw [u_nil, v_nil] at aft,
      rw [list.nil_append, list.append_nil] at aft,
      exact aft,

      all_goals {
        clear_except bef_len,
        rw ← list.length_eq_zero,
        linarith,
      },
    },
    exfalso,
    have nt_match : symbol.nonterminal (big_grammar g₁ g₂).initial = symbol.nonterminal r.input_string.secon,
    {
      have bef_fst := congr_fun (congr_arg list.nth bef) 0,
      have u_nil : u = [], sorry, -- proved above
      have rif_nil : r.input_string.first = [], sorry, -- easy
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
        change sum.inl none = sum.inl (some (sum.inl r₀.input_string.snd.fst)) at inl_match,
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
        change sum.inl none = sum.inl (some (sum.inr r₀.input_string.snd.fst)) at inl_match,
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
        finish,
      },
      {
        clear_except h,
        finish,
      },
      refl,
    },
    rename h i_lt_len_x,
    push_neg at i_lt_len_x,

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
    sorry,
  },
  apply list.take_append_drop,
end

end hard_direction


/-- The class of recursively-enumerable languages is closed under concatenation. -/
theorem RE_of_RE_c_RE (L₁ : language T) (L₂ : language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ * L₂)   :=
begin
  rintro ⟨ ⟨ g₁, h₁ ⟩, ⟨ g₂, h₂ ⟩ ⟩,

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
