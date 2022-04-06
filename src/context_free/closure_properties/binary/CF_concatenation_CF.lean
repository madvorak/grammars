import context_free.closure_properties.CF_helper


variable {T : Type}

private def combined_grammar (gₗ gᵣ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk
  (option (gₗ.nt ⊕ gᵣ.nt))
  none
  ((none, [
    symbol.nonterminal (some (sum.inl (gₗ.initial))),
    symbol.nonterminal (some (sum.inr (gᵣ.initial)))
  ]) :: (
    (list.map rule_of_rule₁ gₗ.rules) ++ (list.map rule_of_rule₂ gᵣ.rules)
  ))

/-- similar to `sink_symbol` -/
private def oN₁_of_N {g₁ g₂ : CF_grammar T} : (combined_grammar g₁ g₂).nt → (option g₁.nt)
| none := none
| (some (sum.inl nonte)) := some nonte
| (some (sum.inr _)) := none


private def g₁g (g₁ g₂ : CF_grammar T) : @lifted_grammar T :=
lifted_grammar.mk g₁ (combined_grammar g₁ g₂) (some ∘ sum.inl) (by {
  -- prove `function.injective (some ∘ sum.inl)` here
  intros x y h,
  apply sum.inl_injective,
  apply option.some_injective,
  exact h,
}) (by {
  -- prove `∀ r ∈ g₁.rules` we have `lift_rule (some ∘ sum.inl) r ∈ list.map rule_of_rule₁ g₁.rules` here
  intros r h,
  apply list.mem_cons_of_mem,
  apply list.mem_append_left,
  rw list.mem_map,
  use r,
  split,
  {
    exact h,
  },
  unfold rule_of_rule₁,
  unfold lift_rule,
  norm_num,
  unfold lift_string,
  unfold lsTN_of_lsTN₁,
  five_steps,
}) (by {
  intro r,
  rintro ⟨ r_in, r_ntype ⟩,
  cases r_in,
  {
    exfalso,
    rw r_in at r_ntype,
    dsimp at r_ntype,
    tauto,
  },
  change r ∈ (list.map rule_of_rule₁ g₁.rules ++ list.map rule_of_rule₂ g₂.rules) at r_in,
  rw list.mem_append at r_in,
  cases r_in,
  {
    rw list.mem_map at r_in,
    rcases r_in with ⟨ r₁, r₁_in, r₁_convert_r ⟩,
    use r₁,
    split,
    {
      exact r₁_in,
    },
    rw ← r₁_convert_r,
    simp only [ lift_rule, rule_of_rule₁, lift_string, lsTN_of_lsTN₁,
                prod.mk.inj_iff, eq_self_iff_true, true_and ],
    five_steps,
  },
  {
    exfalso,
    rw list.mem_map at r_in,
    rcases r_in with ⟨ r₂, r₂_in, r₂_convert_r ⟩,
    rw ← r₂_convert_r at r_ntype,
    unfold rule_of_rule₂ at r_ntype,
    dsimp at r_ntype,
    cases r_ntype with n₁ contr,
    rw option.some_inj at contr,
    tauto,
  },
}) oN₁_of_N (by {
  intros x y h,
  cases x,
  {
    right,
    refl,
  },
  cases x, swap,
  {
    right,
    refl,
  },
  cases y,
  {
    tauto,
  },
  cases y, swap,
  {
    tauto,
  },
  left,
  simp only [oN₁_of_N] at h,
  apply congr_arg,
  apply congr_arg,
  exact h,
}) (by { intro, refl })


private lemma in_language_conca {g₁ g₂ : CF_grammar T} (w : list T)
                                (hyp : w ∈ CF_language g₁ * CF_language g₂) :
  w ∈ CF_language (combined_grammar g₁ g₂) :=
begin
  rw language.mem_mul at hyp,
  rcases hyp with ⟨ u, v, hu, hv, hw ⟩,
  unfold CF_language at *,
  change CF_derives (combined_grammar g₁ g₂)
                    [symbol.nonterminal (combined_grammar g₁ g₂).initial]
                    (list.map symbol.terminal w),

  apply @CF_deri_of_tran_deri T (combined_grammar g₁ g₂) _ [symbol.nonterminal (some (sum.inl (g₁.initial))), symbol.nonterminal (some (sum.inr (g₂.initial)))] _,
  {
    use (none, [symbol.nonterminal (some (sum.inl (g₁.initial))), symbol.nonterminal (some (sum.inr (g₂.initial)))]),
    split,
    {
      apply list.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  rw ← hw,
  rw list.map_append,
  apply @CF_deri_of_deri_deri T (combined_grammar g₁ g₂) _ (list.map symbol.terminal u ++ [symbol.nonterminal (some (sum.inr g₂.initial))]) _,
  {
    change CF_derives (combined_grammar g₁ g₂)
                      ([symbol.nonterminal (some (sum.inl g₁.initial))] ++ [symbol.nonterminal (some (sum.inr g₂.initial))])
                      (list.map symbol.terminal u ++ [symbol.nonterminal (some (sum.inr g₂.initial))]),
    apply CF_derives_with_postfix,

    change CF_derives g₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal u) at hu,
    let gg₁ := g₁g g₁ g₂,
    change CF_derives gg₁.g [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal u),
    
    have bar : [symbol.nonterminal (some (sum.inl g₁.initial))] = list.map (lift_symbol gg₁.lift_nt) [symbol.nonterminal g₁.initial],
    {
      apply list.singleton_eq,
    },
    rw bar,

    have baz : list.map symbol.terminal u = list.map (lift_symbol gg₁.lift_nt) (list.map symbol.terminal u),
    {
      rw list.map_map,
      apply congr_fun,
      apply congr_arg,
      refl,
    },
    rw baz,
    
    exact lift_deri gg₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal u) hu,
  },
  {
    apply CF_derives_with_prefix,

    change CF_derives g₂ [symbol.nonterminal g₂.initial] (list.map symbol.terminal v) at hv,

    sorry,
  },
end


def CF_transforms_leftmost (g : CF_grammar T) (oldWord newWord : list (symbol T g.nt)) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbol T g.nt),
  (oldWord = v ++ [symbol.nonterminal (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w)
  ∧ (∀ s ∈ v, ∃ t : T, s = symbol.terminal t)

def CF_derives_leftmost (g : CF_grammar T) : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CF_transforms_leftmost g)

def CF_generates_str_leftmost (g : CF_grammar T) (str : list (symbol T g.nt)) : Prop :=
CF_derives_leftmost g [symbol.nonterminal g.initial] str

def CF_generates_leftmost (g : CF_grammar T) (word : list T) : Prop :=
CF_generates_str_leftmost g (list.map symbol.terminal word)

lemma CF_generates_iff_generates_leftmost (g : CF_grammar T) (word : list T) :
  CF_generates g word ↔ CF_generates_leftmost g word :=
begin
  unfold CF_generates_leftmost,
  unfold CF_generates,
  unfold CF_generates_str_leftmost,
  unfold CF_generates_str,
  split,
  {
    intro ass,
    -- TODO induction starting with the last step
    sorry,
  },
  {
    intro ass,
    have straight_indu : ∀ w,
      CF_derives_leftmost g [symbol.nonterminal g.initial] w →
        CF_derives g [symbol.nonterminal g.initial] w,
    {
      intros w hw,
      induction hw with x y trash orig ih,
      {
        exact CF_deri_self,
      },
      apply CF_deri_of_deri_tran,
      {
        exact ih,
      },
      rcases orig with ⟨ r, r_in, u, v, transf_correct, unnecessary ⟩,
      use r,
      use r_in,
      use u,
      use v,
      exact transf_correct,
    },
    exact straight_indu (list.map symbol.terminal word) ass,
  }
end

private lemma in_language_comb {g₁ g₂ : CF_grammar T} (w : list T)
                               (hyp : w ∈ CF_language (combined_grammar g₁ g₂)) :
  w ∈ CF_language g₁ * CF_language g₂ :=
begin
  rw language.mem_mul,
  change CF_generates (combined_grammar g₁ g₂) w at hyp,
  rw CF_generates_iff_generates_leftmost at hyp,
  -- 1. unfold the first `CF_transforms_leftmost` step from `hyp`
  -- 2. we will have something like `CF_derives_leftmost (combined_grammar g₁ g₂) [g₁.initial, g₂.initial] (list.map symbol.terminal w)`
  -- 3. use `a` := everything derived from `g₁.initial`
  -- 4. use `b` := everything derived from `g₂.initial`
  -- 5. prove `a ∈ CF_language g₁` by some kind of induction
  -- 6. prove `b ∈ CF_language g₂` by some kind of induction
  -- 7. the remaining goal `a ++ b = w` is trivial
  sorry,
end


/-- The class of context-free languages is closed under concatenation. -/
theorem CF_of_CF_c_CF (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ * L₂)   :=
begin
  rintro ⟨ ⟨ g₁, h₁ ⟩, ⟨ g₂, h₂ ⟩ ⟩,

  use combined_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    -- prove `L₁ * L₂ ⊇ ` here
    intros w hyp,
    rw ← h₁,
    rw ← h₂,
    exact in_language_comb w hyp,
  },
  {
    -- prove `L₁ * L₂ ⊆ ` here
    intros w hyp,
    rw ← h₁ at hyp,
    rw ← h₂ at hyp,
    exact in_language_conca w hyp,
  },
end

#print axioms CF_of_CF_c_CF
