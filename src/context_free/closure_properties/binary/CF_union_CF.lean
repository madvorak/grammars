import context_free.closure_properties.CF_helper


variables {T : Type} {g₁ g₂ : CF_grammar T}

private def union_grammar (gₗ gᵣ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (option (gₗ.nt ⊕ gᵣ.nt)) none (
  (none, [symbol.nonterminal (some (sum.inl (gₗ.initial)))]) ::
  (none, [symbol.nonterminal (some (sum.inr (gᵣ.initial)))]) ::
  ((list.map rule_of_rule₁ gₗ.rules) ++ (list.map rule_of_rule₂ gᵣ.rules))
)


section lifted_grammars

/-- similar to `sink_symbol` -/
private def oN₁_of_N : (union_grammar g₁ g₂).nt → (option g₁.nt)
| none := none
| (some (sum.inl nonte)) := some nonte
| (some (sum.inr _)) := none

/-- similar to `sink_symbol` -/
private def oN₂_of_N : (union_grammar g₁ g₂).nt → (option g₂.nt)
| none := none
| (some (sum.inl _)) := none
| (some (sum.inr nonte)) := some nonte


private def g₁g : @lifted_grammar T :=
lifted_grammar.mk g₁ (union_grammar g₁ g₂) (some ∘ sum.inl) (by {
  intros x y h,
  apply sum.inl_injective,
  apply option.some_injective,
  exact h,
}) (by {
  intros r h,
  apply list.mem_cons_of_mem,
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
    simp only [
        lift_rule, rule_of_rule₁, lift_string, lsTN_of_lsTN₁,
        prod.mk.inj_iff, eq_self_iff_true, true_and
      ],
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

private def g₂g : @lifted_grammar T :=
lifted_grammar.mk g₂ (union_grammar g₁ g₂) (some ∘ sum.inr) (by {
  intros x y h,
  apply sum.inr_injective,
  apply option.some_injective,
  exact h,
}) (by {
  intros r h,
  apply list.mem_cons_of_mem,
  apply list.mem_cons_of_mem,
  apply list.mem_append_right,
  rw list.mem_map,
  use r,
  split,
  {
    exact h,
  },
  unfold rule_of_rule₂,
  unfold lift_rule,
  norm_num,
  unfold lift_string,
  unfold lsTN_of_lsTN₂,
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
    exfalso,
    rw list.mem_map at r_in,
    rcases r_in with ⟨ r₁, r₁_in, r₁_convert_r ⟩,
    rw ← r₁_convert_r at r_ntype,
    unfold rule_of_rule₁ at r_ntype,
    dsimp at r_ntype,
    cases r_ntype with n₂ contr,
    rw option.some_inj at contr,
    tauto,
  },
  {
    rw list.mem_map at r_in,
    rcases r_in with ⟨ r₂, r₂_in, r₂_convert_r ⟩,
    use r₂,
    split,
    {
      exact r₂_in,
    },
    rw ← r₂_convert_r,
    simp only [ lift_rule, rule_of_rule₂, lift_string, lsTN_of_lsTN₂,
                prod.mk.inj_iff, eq_self_iff_true, true_and ],
    five_steps,
  },
}) oN₂_of_N (by {
  intros x y h,
  cases x,
  {
    right,
    refl,
  },
  cases x,
  {
    right,
    refl,
  },
  cases y,
  {
    tauto,
  },
  cases y,
  {
    tauto,
  },
  left,
  simp only [oN₂_of_N] at h,
  apply congr_arg,
  apply congr_arg,
  exact h,
}) (by { intro, refl })

end lifted_grammars


section lemmata_subset

private lemma deri₁_more :
  ∀ output : list (symbol T g₁.nt),
    CF_derives g₁ [symbol.nonterminal g₁.initial] output →
      CF_derives
        (union_grammar g₁ g₂)
        (lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial])
        (lsTN_of_lsTN₁ output) :=
begin
  intros outp ass,
  let gg₁ := @g₁g T g₁ g₂,
  change CF_derives gg₁.g (lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial]) (lsTN_of_lsTN₁ outp),
  have techni : lsTN_of_lsTN₁ = lift_string gg₁.lift_nt,
  {
    unfold lsTN_of_lsTN₁,
    unfold lift_string,
    ext1 w,
    five_steps,
  },
  rw techni,
  exact lift_deri gg₁ [symbol.nonterminal g₁.initial] outp ass,
end

private lemma deri₂_more :
  ∀ output : list (symbol T g₂.nt),
    CF_derives g₂ [symbol.nonterminal g₂.initial] output →
      CF_derives
        (union_grammar g₁ g₂)
        (lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial])
        (lsTN_of_lsTN₂ output) :=
begin
  intros outp ass,
  let gg₂ := @g₂g T g₁ g₂,
  change CF_derives gg₂.g (lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial]) (lsTN_of_lsTN₂ outp),
  have techni : lsTN_of_lsTN₂ = lift_string gg₂.lift_nt,
  {
    unfold lsTN_of_lsTN₂,
    unfold lift_string,
    ext1 w,
    five_steps,
  },
  rw techni,
  exact lift_deri gg₂ [symbol.nonterminal g₂.initial] outp ass,
end

private lemma in_union_of_in_first (w : list T) :
  w ∈ CF_language g₁  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
begin
  intro assum,

  have deri_start :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal none]
      [symbol.nonterminal (some (sum.inl g₁.initial))],
  {
    apply CF_deri_of_tran,
    use (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]),
    split,
    {
      change (none, [symbol.nonterminal (some (sum.inl g₁.initial))]) ∈ (
        (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
        (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
        ((list.map rule_of_rule₁ g₁.rules) ++ (list.map rule_of_rule₂ g₂.rules))
      ),
      apply list.mem_cons_self,
    },
    use [[], []],
    simp,
  },

  have deri_rest :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal (some (sum.inl g₁.initial))]
      (list.map symbol.terminal w),
  {
    have beginning :
      [symbol.nonterminal (some (sum.inl g₁.initial))] =
      lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial],
    {
      unfold lsTN_of_lsTN₁,
      change
        [symbol.nonterminal (some (sum.inl g₁.initial))] =
        [sTN_of_sTN₁ (symbol.nonterminal g₁.initial)],
      unfold sTN_of_sTN₁,
    },
    have ending :
      (list.map symbol.terminal w) =
      lsTN_of_lsTN₁ (list.map symbol.terminal w),
    {
      ext1,
      unfold lsTN_of_lsTN₁,
      simp,
      apply congr_arg,
      refl,
    },
    rw beginning,
    rw ending,
    exact deri₁_more (list.map symbol.terminal w) assum,
  },

  unfold CF_language,
  change CF_generates_str (union_grammar g₁ g₂) (list.map symbol.terminal w),
  unfold CF_generates_str,
  unfold CF_derives,
  apply CF_deri_of_deri_deri,
  {
    finish, -- uses `deri_start` here
  },
  exact deri_rest,
end

private lemma in_union_of_in_second (w : list T) :
  w ∈ CF_language g₂  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
begin
  intro assum,

  have deri_start :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal none]
      [symbol.nonterminal (some (sum.inr g₂.initial))],
  {
    apply CF_deri_of_tran,
    use (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]),
    split,
    {
      change (none, [symbol.nonterminal (some (sum.inr g₂.initial))]) ∈ (
        (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
        (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
        ((list.map rule_of_rule₁ g₁.rules) ++ (list.map rule_of_rule₂ g₂.rules))
      ),
      apply list.mem_cons_of_mem,
      apply list.mem_cons_self,
    },
    use [[], []],
    simp,
  },

  have deri_rest :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal (some (sum.inr g₂.initial))]
      (list.map symbol.terminal w),
  {
    have beginning :
      [symbol.nonterminal (some (sum.inr g₂.initial))] =
      lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial],
    {
      unfold lsTN_of_lsTN₂,
      change
        [symbol.nonterminal (some (sum.inr g₂.initial))] =
        [sTN_of_sTN₂ (symbol.nonterminal g₂.initial)],
      unfold sTN_of_sTN₂,
    },
    have ending :
      (list.map symbol.terminal w) =
      lsTN_of_lsTN₂ (list.map symbol.terminal w),
    {
      ext1,
      unfold lsTN_of_lsTN₂,
      simp,
      apply congr_arg,
      refl,
    },
    rw beginning,
    rw ending,
    exact deri₂_more (list.map symbol.terminal w) assum,
  },

  unfold CF_language,
  change CF_generates_str (union_grammar g₁ g₂) (list.map symbol.terminal w),
  unfold CF_generates_str,
  unfold CF_derives,
  apply CF_deri_of_deri_deri,
  {
    finish, -- uses `deri_start` here
  },
  exact deri_rest,
end

end lemmata_subset


section lemmata_supset

meta def good_singleton : tactic unit := `[
  unfold good_string,
  intros letter in_singleton,
  rw list.mem_singleton at in_singleton,
  rw in_singleton,
  unfold good_letter
]

private lemma in_language_left_case_of_union
    (w : list T)
    (hypo : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w)) :
  w ∈ CF_language g₁ :=
begin
  unfold CF_language,
  change CF_generates_str g₁ (list.map symbol.terminal w),
  unfold CF_generates_str,

  let gg₁ := @g₁g T g₁ g₂,

  have bar :
    [symbol.nonterminal g₁.initial] =
    (sink_string gg₁.sink_nt [symbol.nonterminal (some (sum.inl g₁.initial))]),
  {
    unfold sink_string,
    refl,
  },
  rw bar,

  have baz : list.map symbol.terminal w = sink_string gg₁.sink_nt (list.map symbol.terminal w),
  {
    unfold sink_string,
    rw list.filter_map_map,
    change list.map symbol.terminal w = list.filter_map (λ x, (sink_symbol gg₁.sink_nt ∘ symbol.terminal) x) w,
    convert_to list.map symbol.terminal w = list.filter_map (λ x, option.some (symbol.terminal x)) w,
    change list.map symbol.terminal w = list.filter_map (option.some ∘ symbol.terminal) w,
    clear hypo,
    induction w,
    {
      refl,
    },
    rw list.map,
    convert_to symbol.terminal w_hd :: list.map symbol.terminal w_tl =
               symbol.terminal w_hd :: list.filter_map (some ∘ symbol.terminal) w_tl,
    norm_num,
    exact w_ih,
  },
  rw baz,

  exact (sink_deri gg₁ [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w) hypo (by {
    good_singleton,
    use g₁.initial,
    refl,
  })).left,
end

private lemma in_language_right_case_of_union (w : list T)
  (hypo : CF_derives (union_grammar g₁ g₂)
    [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal w)) :
  w ∈ CF_language g₂ :=
begin
  unfold CF_language,
  change CF_generates_str g₂ (list.map symbol.terminal w),
  unfold CF_generates_str,

  let gg₂ := @g₂g T g₁ g₂,

  have bar :
    [symbol.nonterminal g₂.initial] =
    (sink_string gg₂.sink_nt [symbol.nonterminal (some (sum.inr g₂.initial))]),
  {
    unfold sink_string,
    refl,
  },
  rw bar,

  have baz : list.map symbol.terminal w = sink_string gg₂.sink_nt (list.map symbol.terminal w),
  {
    unfold sink_string,
    rw list.filter_map_map,
    change list.map symbol.terminal w = list.filter_map (λ x, (sink_symbol gg₂.sink_nt ∘ symbol.terminal) x) w,
    convert_to list.map symbol.terminal w = list.filter_map (λ x, option.some (symbol.terminal x)) w,
    change list.map symbol.terminal w = list.filter_map (option.some ∘ symbol.terminal) w,
    clear hypo,
    induction w,
    {
      refl,
    },
    rw list.map,
    convert_to symbol.terminal w_hd :: list.map symbol.terminal w_tl =
               symbol.terminal w_hd :: list.filter_map (some ∘ symbol.terminal) w_tl,
    norm_num,
    exact w_ih,
  },
  rw baz,

  exact (sink_deri gg₂ [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal w) hypo (by {
    good_singleton,
    use g₂.initial,
    refl,
  })).left,
end

private lemma both_empty
    (u v: list (symbol T (union_grammar g₁ g₂).nt))
    (a : (symbol T (union_grammar g₁ g₂).nt))
    (bef: [symbol.nonterminal (union_grammar g₁ g₂).initial] = u ++ [a] ++ v) :
  u = []  ∧  v = [] :=
begin
  have len := congr_arg list.length bef,
  rw list.length_append at len,
  simp at len,
  split,
  {
    by_contradiction,
    rw ← list.length_eq_zero at h,
    exact nat.not_succ_le_self 1 (by calc
      1 = (u.length + 1) + v.length : len
    ... = u.length + (1 + v.length) : add_assoc (list.length u) 1 (list.length v)
    ... ≥ 1 + (1 + v.length)        : add_le_add (nat.one_le_iff_ne_zero.mpr h) (le_of_eq rfl)
    ... = (1 + 1) + v.length        : eq.symm (add_assoc 1 1 (list.length v))
    ... ≥ 1 + 1 + 0                 : le_self_add
    ... = 2                         : rfl),
  },
  {
    by_contradiction,
    rw ← list.length_eq_zero at h,
    exact nat.not_succ_le_self 1 (by calc
      1 = (u.length + 1) + v.length : len
    ... ≥ (u.length + 1) + 1        : add_le_add (le_of_eq rfl) (nat.one_le_iff_ne_zero.mpr h)
    ... = u.length + (1 + 1)        : add_assoc (list.length u) 1 1
    ... ≥ 0 + (1 + 1)               : le_add_self
    ... = (0 + 1) + 1               : eq.symm (add_assoc 0 1 1)
    ... = 2                         : rfl),
  },
end

private lemma in_language_impossible_case_of_union
    (w : list T)
    (rule : (union_grammar g₁ g₂).nt × list (symbol T (union_grammar g₁ g₂).nt))
    (u v: list (symbol T (union_grammar g₁ g₂).nt))
    (hu : u = []) (hv : v = [])
    (bef: [symbol.nonterminal (union_grammar g₁ g₂).initial] = u ++ [symbol.nonterminal rule.fst] ++ v)
    (sbi : rule ∈ (list.map rule_of_rule₁ g₁.rules ++ list.map rule_of_rule₂ g₂.rules)) :
  w ∈ CF_language g₁ ∨ w ∈ CF_language g₂ :=
begin
  exfalso,
  rw hu at bef,
  rw hv at bef,
  rw list.nil_append at bef,
  rw list.append_nil at bef,
  change [symbol.nonterminal none] = [symbol.nonterminal rule.fst] at bef,
  have rule_root : rule.fst = none,
  {
    finish,
  },
  rw list.mem_append at sbi,
  cases sbi;
  finish,
end

private lemma in_language_of_in_union (w : list T) :
  w ∈ CF_language (union_grammar g₁ g₂)   →   w ∈ CF_language g₁  ∨  w ∈ CF_language g₂   :=
begin
  intro ass,

  cases CF_tran_or_id_of_deri ass with impossible h,
  {
    exfalso,
    have zeroth := congr_arg (λ p, list.nth p 0) impossible,
    simp at zeroth,
    cases (w.nth 0);
    finish,
  },
  rcases h with ⟨ S₁, deri_head, deri_tail ⟩,
  rcases deri_head with ⟨ rule, ruleok, u, v, h_bef, h_aft ⟩,

  rw h_aft at deri_tail,
  cases both_empty u v (symbol.nonterminal rule.fst) h_bef with u_nil v_nil,

  cases ruleok with g₁S r_rest,
  {
    left,
    rw g₁S at *,
    simp at *,
    rw u_nil at deri_tail,
    rw v_nil at deri_tail,
    simp at deri_tail,
    exact in_language_left_case_of_union w deri_tail,
  },
  cases r_rest with g₂S r_imposs,
  {
    right,
    rw g₂S at *,
    simp at *,
    rw u_nil at deri_tail,
    rw v_nil at deri_tail,
    simp at deri_tail,
    exact in_language_right_case_of_union w deri_tail,
  },
  exact in_language_impossible_case_of_union w
    rule u v u_nil v_nil h_bef r_imposs,
end

end lemmata_supset


/-- The class of context-free languages is closed under union. -/
theorem CF_of_CF_u_CF {T : Type} (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ + L₂)   :=
begin
  intro input,
  cases input with cf₁ cf₂,
  cases cf₁ with g₁ h₁,
  cases cf₂ with g₂ h₂,

  use union_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    -- prove `L₁ + L₂ ⊇ `
    intros w hyp,
    simp,
    rw ← h₁,
    rw ← h₂,
    exact in_language_of_in_union w hyp,
  },
  {
    -- prove `L₁ + L₂ ⊆ `
    intros w hyp,
    rw language.mem_add at hyp,
    cases hyp with case₁ case₂,
    {
      rw ← h₁ at case₁,
      exact in_union_of_in_first w case₁,
    },
    {
      rw ← h₂ at case₂,
      exact in_union_of_in_second w case₂,
    },
  }
end
