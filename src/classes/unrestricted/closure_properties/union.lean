import classes.unrestricted.lifting


variables {T : Type}

protected def union_grammar (g₁ g₂ : grammar T) : grammar T :=
grammar.mk (option (g₁.nt ⊕ g₂.nt)) none (
  ⟨ [], none, [], [symbol.nonterminal (some (sum.inl (g₁.initial)))] ⟩ :: (
  ⟨ [], none, [], [symbol.nonterminal (some (sum.inr (g₂.initial)))] ⟩ :: (
  (list.map (lift_rule (some ∘ sum.inl)) g₁.rules) ++
  (list.map (lift_rule (some ∘ sum.inr)) g₂.rules)
)))

variables {g₁ g₂ : grammar T}

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (option g₁.nt)
| none               := none
| (some (sum.inl n)) := some n
| (some (sum.inr _)) := none

private def oN₂_of_N : (union_grammar g₁ g₂).nt → (option g₂.nt)
| none               := none
| (some (sum.inl _)) := none
| (some (sum.inr n)) := some n


private def lg₁ : lifted_grammar T :=
lifted_grammar.mk g₁ (union_grammar g₁ g₂) (option.some ∘ sum.inl) oN₁_of_N (by
{
  intros x y h,
  apply sum.inl_injective,
  apply option.some_injective,
  exact h,
}
) (by
{
  intros x y hyp,
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
    rw hyp,
    right,
    refl,
  },
  cases y, swap,
  {
    tauto,
  },
  left,
  simp only [oN₁_of_N] at hyp,
  apply congr_arg,
  apply congr_arg,
  exact hyp,
}
) (by
{
  intro,
  refl,
}
) (by
{
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
  refl,
}
) (by
{
  rintros r ⟨rin, n₀, rnt⟩,
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    exact option.no_confusion rnt,
  },
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    exact option.no_confusion rnt,
  },
  change r ∈ (
      list.map (lift_rule (some ∘ sum.inl)) g₁.rules ++
      list.map (lift_rule (some ∘ sum.inr)) g₂.rules
    ) at rin,
  rw list.mem_append at rin,
  cases rin,
  {
    rw list.mem_map at rin,
    rcases rin with ⟨r₁, r₁_in, r₁_lift⟩,
    use r₁,
    split,
    {
      exact r₁_in,
    },
    exact r₁_lift,
  },
  {
    exfalso,
    rw list.mem_map at rin,
    rcases rin with ⟨r₂, r₂_in, r₂_lift⟩,
    rw ←r₂_lift at rnt,
    unfold lift_rule at rnt,
    dsimp only at rnt,
    have rnti := option.some.inj rnt,
    exact sum.no_confusion rnti,
  },
})

private def lg₂ : lifted_grammar T :=
lifted_grammar.mk g₂ (union_grammar g₁ g₂) (option.some ∘ sum.inr) oN₂_of_N (by
{
  intros x y h,
  apply sum.inr_injective,
  apply option.some_injective,
  exact h,
}
) (by
{
  intros x y hyp,
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
    right,
    rw hyp,
    refl,
  },
  cases y,
  {
    tauto,
  },
  left,
  simp only [oN₂_of_N] at hyp,
  apply congr_arg,
  apply congr_arg,
  exact hyp,
}
) (by
{
  intro,
  refl,
}
) (by
{
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
  refl,
}
) (by
{
  rintros r ⟨rin, n₀, rnt⟩,
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    exact option.no_confusion rnt,
  },
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    exact option.no_confusion rnt,
  },
  change r ∈ (
      list.map (lift_rule (some ∘ sum.inl)) g₁.rules ++
      list.map (lift_rule (some ∘ sum.inr)) g₂.rules
    ) at rin,
  rw list.mem_append at rin,
  cases rin,
  {
    exfalso,
    rw list.mem_map at rin,
    rcases rin with ⟨r₁, r₁_in, r₁_lift⟩,
    rw ←r₁_lift at rnt,
    unfold lift_rule at rnt,
    dsimp only at rnt,
    have rnti := option.some.inj rnt,
    exact sum.no_confusion rnti,
  },
  {
    rw list.mem_map at rin,
    rcases rin with ⟨r₂, r₂_in, r₂_lift⟩,
    use r₂,
    split,
    {
      exact r₂_in,
    },
    exact r₂_lift,
  },
})


protected lemma in_L₁_or_L₂_of_in_union {w : list T} (ass : w ∈ grammar_language (union_grammar g₁ g₂)) :
  w ∈ grammar_language g₁  ∨  w ∈ grammar_language g₂  :=
begin
  unfold grammar_language at ass ⊢,
  rw set.mem_set_of_eq at ⊢ ass,
  rw set.mem_set_of_eq at ⊢,
  unfold grammar_generates at ass ⊢,
  have hyp := grammar_tran_or_id_of_deri ass,
  clear ass,
  cases hyp,
  {
    exfalso,
    have zeroth := congr_fun (congr_arg list.nth hyp) 0,
    cases w,
    {
      exact option.no_confusion zeroth,
    },
    {
      rw [list.nth, list.map_cons, list.nth] at zeroth,
      have nt_eq_ter := option.some.inj zeroth,
      exact symbol.no_confusion nt_eq_ter,
    },
  },
  rcases hyp with ⟨i, ⟨r, rin, u, v, bef, aft⟩, deri⟩,

  have uv_nil :  u = []  ∧  v = [],
  {
    have bef_len := congr_arg list.length bef,
    clear_except bef_len,
    rw list.length_singleton at bef_len,
    repeat {
      rw list.length_append at bef_len
    },
    rw list.length_singleton at bef_len,
    split;
    {
      rw ←list.length_eq_zero,
      linarith,
    },
  },
  rw [uv_nil.1, list.nil_append, uv_nil.2, list.append_nil] at bef aft,

  have same_nt : (union_grammar g₁ g₂).initial = r.input_N,
  {
    clear_except bef,
    have elemeq : [symbol.nonterminal (union_grammar g₁ g₂).initial] = [symbol.nonterminal r.input_N],
    {
      have bef_len := congr_arg list.length bef,
      rw [list.length_append_append, list.length_singleton, list.length_singleton] at bef_len,
      have rl_first : r.input_L.length = 0,
      {
        clear_except bef_len,
        linarith,
      },
      have rl_third : r.input_R.length = 0,
      {
        clear_except bef_len,
        linarith,
      },
      rw list.length_eq_zero at rl_first rl_third,
      rw [rl_first, rl_third] at bef,
      exact bef,
    },
    exact symbol.nonterminal.inj (list.head_eq_of_cons_eq elemeq),
  },

  cases rin,
  {
    rw rin at aft,
    dsimp only at aft,
    rw aft at deri,
    left,

    have sinked := sink_deri lg₁ deri,
    clear_except sinked,
    specialize sinked (by {
      unfold good_string,
      simp only [list.mem_singleton, forall_eq],
      use g₁.initial,
      refl,
    }),
    convert sinked,

    unfold sink_string,
    rw list.filter_map_map,
    convert_to list.map symbol.terminal w = list.filter_map (option.some ∘ symbol.terminal) w,
    rw ←list.filter_map_map,
    rw list.filter_map_some,
  },
  cases rin,
  {
    rw rin at aft,
    dsimp only at aft,
    rw aft at deri,
    right,

    have sinked := sink_deri lg₂ deri,
    clear_except sinked,
    specialize sinked (by {
      unfold good_string,
      simp only [list.mem_singleton, forall_eq],
      use g₂.initial,
      refl,
    }),
    convert sinked,

    unfold sink_string,
    rw list.filter_map_map,
    convert_to list.map symbol.terminal w = list.filter_map (option.some ∘ symbol.terminal) w,
    rw ←list.filter_map_map,
    rw list.filter_map_some,
  },
  exfalso,
  clear_except rin bef,

  change r ∈ (
      list.map (lift_rule (some ∘ sum.inl)) g₁.rules ++
      list.map (lift_rule (some ∘ sum.inr)) g₂.rules
    ) at rin,
  rw list.mem_append at rin,
  cases rin;
  rw list.mem_map at rin;
  rcases rin with ⟨ror, rri, rli⟩;
  rw ←rli at bef;
  clear_except bef,

  {
    have inb := congr_arg
      (λ z, symbol.nonterminal (lift_rule (option.some ∘ sum.inl) ror).input_N ∈ z)
      bef,
    apply false_of_true_eq_false,
    convert inb.symm,
    {
      simp,
    },
    rw list.mem_singleton,
    rw symbol.nonterminal.inj_eq,
    change false = (_ = option.none),
    unfold lift_rule,
    clear_except,
    norm_num,
  },
  {
    have inb := congr_arg
      (λ z, symbol.nonterminal (lift_rule (option.some ∘ sum.inr) ror).input_N ∈ z)
      bef,
    apply false_of_true_eq_false,
    convert inb.symm,
    {
      simp,
    },
    rw list.mem_singleton,
    rw symbol.nonterminal.inj_eq,
    change false = (_ = option.none),
    unfold lift_rule,
    clear_except,
    norm_num,
  },
end


protected lemma in_union_of_in_L₁ {w : list T} (ass : w ∈ grammar_language g₁) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
begin
  unfold grammar_language at ass ⊢,
  rw set.mem_set_of_eq at ass ⊢,
  unfold grammar_generates at ass ⊢,
  apply grammar_deri_of_tran_deri,
  {
    use ⟨ [], none, [], [symbol.nonterminal (some (sum.inl (g₁.initial)))] ⟩,
    split,
    {
      apply list.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  dsimp only,
  rw [list.nil_append, list.append_nil],
  have lifted := lift_deri (@lg₁ _ _ g₂) ass,
  change
    grammar_derives lg₁.g
      (lift_string lg₁.lift_nt [symbol.nonterminal g₁.initial])
      (list.map symbol.terminal w),
  have equiv_out : (lift_string lg₁.lift_nt (list.map symbol.terminal w)) = (list.map symbol.terminal w),
  {
    unfold lift_string,
    rw list.map_map,
    refl,
  },
  rw equiv_out at lifted,
  exact lifted,
end

protected lemma in_union_of_in_L₂ {w : list T} (ass : w ∈ grammar_language g₂) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
begin
  unfold grammar_language at ass ⊢,
  rw set.mem_set_of_eq at ass ⊢,
  unfold grammar_generates at ass ⊢,
  apply grammar_deri_of_tran_deri,
  {
    use ⟨ [], none, [], [symbol.nonterminal (some (sum.inr (g₂.initial)))] ⟩,
    split,
    {
      apply list.mem_cons_of_mem,
      apply list.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  dsimp only,
  rw [list.nil_append, list.append_nil],
  have lifted := lift_deri (@lg₂ _ g₁ _) ass,
  change
    grammar_derives lg₂.g
      (lift_string lg₂.lift_nt [symbol.nonterminal g₂.initial])
      (list.map symbol.terminal w),
  have equiv_out : (lift_string lg₂.lift_nt (list.map symbol.terminal w)) = (list.map symbol.terminal w),
  {
    unfold lift_string,
    rw list.map_map,
    refl,
  },
  rw equiv_out at lifted,
  exact lifted,
end


/-- The class of recursively-enumerable languages is closed under union. -/
theorem RE_of_RE_u_RE (L₁ : language T) (L₂ : language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ + L₂)   :=
begin
  rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩,

  unfold is_RE,
  use union_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    intros w ass,
    rw language.mem_add,
    rw [←h₁, ←h₂],
    exact in_L₁_or_L₂_of_in_union ass,
  },
  {
    intros w ass,
    cases ass with case₁ case₂,
    {
      rw ←h₁ at case₁,
      exact in_union_of_in_L₁ case₁,
    },
    {
      rw ←h₂ at case₂,
      exact in_union_of_in_L₂ case₂,
    },
  },
end
