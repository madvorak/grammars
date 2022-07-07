import unrestricted.grammarLiftSink


variables {T : Type} [decidable_eq T]

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

private def as_terminal {N : Type} : symbol T N → option T
| (symbol.terminal t)    := some t
| (symbol.nonterminal _) := none

private def all_used_terminals (g : grammar T) : list T :=
list.dedup (list.filter_map as_terminal (
  list.join (list.map grule.output_string g.rules)))

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


private lemma in_concatenated_of_in_big
    {g₁ g₂ : grammar T}
    {w : list T}
    (ass : w ∈ grammar_language (big_grammar g₁ g₂)) :
  w ∈ grammar_language g₁ * grammar_language g₂ :=
begin
  rw language.mem_mul,
  sorry,
end


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

lemma two_singletons_of_doubleton {α : Type} {a b : α} : [a, b] = [a] ++ [b] :=
rfl

lemma append_of_quadrupledot {α : Type} (a : α) (l : list α) : a :: l = [a] ++ l :=
rfl

private lemma substitute_terminals {g₁ g₂ : grammar T} {w : list T}
    (legit_terminals : ∀ t ∈ w, ∃ (a : grule T g₁.nt),
      a ∈ g₁.rules ∧ symbol.terminal t ∈ a.output_string) :
  grammar_derives (big_grammar g₁ g₂)
    (list.map (symbol.nonterminal ∘ sum.inr ∘ sum.inl) w)
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
      ([(symbol.nonterminal ∘ sum.inr ∘ sum.inl) d] ++ list.map (symbol.nonterminal ∘ sum.inr ∘ sum.inl) l)
      ([symbol.terminal d] ++ list.map (symbol.nonterminal ∘ sum.inr ∘ sum.inl) l),
  {
    use grule.mk ([], sum.inr (sum.inl d), []) [symbol.terminal d],
    split,
    {
      change _ ∈ list.cons _ _,
      apply list.mem_cons_of_mem,
      apply list.mem_append_right,
      apply list.mem_append_left,
      unfold rules_for_terminals₁,
      rw list.mem_map,
      use d,
      split,
      {
        unfold all_used_terminals,
        rw list.mem_dedup,
        rw list.mem_filter_map,
        use symbol.terminal d,
        split,
        {
          rw list.mem_join,
          obtain ⟨r, rin, d_eq⟩ := legit_terminals d (list.mem_cons_self d l),
          use r.output_string,
          split,
          {
            apply list.mem_map_of_mem,
            exact rin,
          },
          {
            exact d_eq,
          },
        },
        {
          refl,
        },
      },
      refl,
    },
    use [[], list.map (symbol.nonterminal ∘ sum.inr ∘ sum.inl) l],
    split;
    refl,
  },
  apply grammar_deri_of_tran_deri step_head,
  apply grammar_derives_with_prefix,
  apply ih,
  intros t tin,
  apply legit_terminals t,
  exact list.mem_cons_of_mem d tin,
end

private lemma grammar_generates_only_legit_terminals -- this lemma is kinda general
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
    exact ih (by {
      rw bef,
      repeat {
        rw list.mem_append,
        left,
      },
      exact symbol_derived,
    }),
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
    exact ih (by {
      rw bef,
      rw list.mem_append,
      right,
      exact symbol_derived,
    }),
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
      apply substitute_terminals,
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
  },
  {
    clear_except hv,
    apply grammar_derives_with_prefix,
    sorry,
  },
end

/-- The class of recursively-enumerable languages is closed under concatenation. -/
theorem RE_of_RE_c_RE (L₁ : language T) (L₂ : language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ * L₂)   :=
begin
  rintro ⟨ ⟨ g₁, h₁ ⟩, ⟨ g₂, h₂ ⟩ ⟩,

  use big_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    -- prove `L₁ * L₂ ⊇ ` here
    intros w hyp,
    rw ← h₁,
    rw ← h₂,
    exact in_concatenated_of_in_big hyp,
  },
  {
    -- prove `L₁ * L₂ ⊆ ` here
    intros w hyp,
    rw ← h₁ at hyp,
    rw ← h₂ at hyp,
    exact in_big_of_in_concatenated hyp,
  },
end
