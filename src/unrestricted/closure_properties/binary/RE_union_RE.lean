import unrestricted.grammarLiftSink


section RE_union_RE_aux

parameters {T : Type} [decidable_eq T] {g₁ g₂ : grammar T}

private def union_grammar : grammar T :=
grammar.mk (option (g₁.nt ⊕ g₂.nt)) none (
  ⟨ ([], none, []), [symbol.nonterminal (some (sum.inl (g₁.initial)))] ⟩ ::
  ⟨ ([], none, []), [symbol.nonterminal (some (sum.inr (g₂.initial)))] ⟩ ::
  ((list.map (lift_rule_ (some ∘ sum.inl)) g₁.rules) ++
   (list.map (lift_rule_ (some ∘ sum.inr)) g₂.rules)
))


private def oN₁_of_N : union_grammar.nt → (option g₁.nt)
| none               := none
| (some (sum.inl n)) := some n
| (some (sum.inr _)) := none

private def oN₂_of_N : union_grammar.nt → (option g₂.nt)
| none               := none
| (some (sum.inl _)) := none
| (some (sum.inr n)) := some n


private def lg₁ : lifted_grammar_ T :=
lifted_grammar_.mk g₁ union_grammar (option.some ∘ sum.inl) oN₁_of_N (by
{
  intros x y h,
  apply sum.inl_injective,
  apply option.some_injective,
  exact h,
}
) (by
{
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
  rintros r ⟨ rin, n₀, rnt ⟩,
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    dsimp at rnt,
    clear_except rnt,
    tauto,
  },
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    dsimp at rnt,
    clear_except rnt,
    tauto,
  },
  change r ∈ (
      list.map (lift_rule_ (some ∘ sum.inl)) g₁.rules ++
      list.map (lift_rule_ (some ∘ sum.inr)) g₂.rules
    ) at rin,
  rw list.mem_append at rin,
  cases rin,
  {
    rw list.mem_map at rin,
    rcases rin with ⟨ r₁, r₁_in, r₁_lift ⟩,
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
    rcases rin with ⟨ r₂, r₂_in, r₂_lift ⟩,
    rw ← r₂_lift at rnt,
    unfold lift_rule_ at rnt,
    dsimp at rnt,
    have rnti := option.some.inj rnt,
    clear_except rnti,
    tauto,
  },
})

private def lg₂ : lifted_grammar_ T :=
lifted_grammar_.mk g₂ union_grammar (option.some ∘ sum.inr) oN₂_of_N (by
{
  intros x y h,
  apply sum.inr_injective,
  apply option.some_injective,
  exact h,
}
) (by
{
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
  rintros r ⟨ rin, n₀, rnt ⟩,
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    dsimp at rnt,
    clear_except rnt,
    tauto,
  },
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    dsimp at rnt,
    clear_except rnt,
    tauto,
  },
  change r ∈ (
      list.map (lift_rule_ (some ∘ sum.inl)) g₁.rules ++
      list.map (lift_rule_ (some ∘ sum.inr)) g₂.rules
    ) at rin,
  rw list.mem_append at rin,
  cases rin,
  {
    exfalso,
    rw list.mem_map at rin,
    rcases rin with ⟨ r₁, r₁_in, r₁_lift ⟩,
    rw ← r₁_lift at rnt,
    unfold lift_rule_ at rnt,
    dsimp at rnt,
    have rnti := option.some.inj rnt,
    clear_except rnti,
    tauto,
  },
  {
    rw list.mem_map at rin,
    rcases rin with ⟨ r₂, r₂_in, r₂_lift ⟩,
    use r₂,
    split,
    {
      exact r₂_in,
    },
    exact r₂_lift,
  },
})


private lemma in_L₁_or_L₂_of_in_union {w : list T} (ass : w ∈ grammar_language union_grammar) :
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
      dsimp at zeroth,
      clear_except zeroth,
      tauto,
    },
    {
      dsimp at zeroth,
      have nt_eq_ter := option.some.inj zeroth,
      clear_except nt_eq_ter,
      tauto,
    }
  },
  rcases hyp with ⟨ i, ⟨ rul, rin, u, v, bef, aft ⟩, deri ⟩,

  have uv_nil :  u = []  ∧  v = [],
  {
    have bef_len := congr_arg list.length bef,
    clear_except bef_len,
    rw list.length_singleton at bef_len,
    repeat { rw list.length_append at bef_len },
    rw list.length_singleton at bef_len,
    split,
    {
      have u_len_0 : u.length = 0,
      {
        linarith,
      },
      rw ← list.length_eq_zero,
      exact u_len_0,
    },
    {
      have v_len_0 : v.length = 0,
      {
        linarith,
      },
      rw ← list.length_eq_zero,
      exact v_len_0,
    },
  },
  rw [ uv_nil.1, list.nil_append, uv_nil.2, list.append_nil ] at bef aft,

  have same_nt : union_grammar.initial = rul.input_string.secon,
  {
    clear_except bef,
    have elemeq : [symbol.nonterminal union_grammar.initial] = [symbol.nonterminal rul.input_string.secon],
    {
      have bef_len := congr_arg list.length bef,
      rw [ list.length_append_append, list.length_singleton, list.length_singleton ] at bef_len,
      have rl_first : rul.input_string.first.length = 0,
      {
        clear_except bef_len,
        linarith,
      },
      have rl_third : rul.input_string.third.length = 0,
      {
        clear_except bef_len,
        linarith,
      },
      rw list.length_eq_zero at rl_first rl_third,
      rw [ rl_first, rl_third ] at bef,
      exact bef,
    },
    exact symbol.nonterminal.inj (list.head_eq_of_cons_eq elemeq),
  },

  cases rin,
  {
    rw rin at aft,
    dsimp at aft,
    rw aft at deri,
    left,

    have sinked := sink_deri_ lg₁ deri,
    clear_except sinked,
    specialize sinked (by {
      unfold good_string_,
      simp only [ list.mem_singleton, forall_eq ],
      use g₁.initial,
      refl,
    }),
    convert sinked,

    unfold sink_string_,
    rw list.filter_map_map,
    convert_to list.map symbol.terminal w = list.filter_map (option.some ∘ symbol.terminal) w,
    rw ← list.filter_map_map,
    rw list.filter_map_some,
  },
  cases rin,
  {
    rw rin at aft,
    dsimp at aft,
    rw aft at deri,
    right,

    have sinked := sink_deri_ lg₂ deri,
    clear_except sinked,
    specialize sinked (by {
      unfold good_string_,
      simp only [ list.mem_singleton, forall_eq ],
      use g₂.initial,
      refl,
    }),
    convert sinked,

    unfold sink_string_,
    rw list.filter_map_map,
    convert_to list.map symbol.terminal w = list.filter_map (option.some ∘ symbol.terminal) w,
    rw ← list.filter_map_map,
    rw list.filter_map_some,
  },
  exfalso,
  clear_except rin bef,

  change rul ∈ (
      list.map (lift_rule_ (some ∘ sum.inl)) g₁.rules ++
      list.map (lift_rule_ (some ∘ sum.inr)) g₂.rules
    ) at rin,
  rw list.mem_append at rin,
  cases rin;
  rw list.mem_map at rin;
  rcases rin with ⟨ ror, rri, rli ⟩;
  rw ← rli at bef;
  clear_except bef,

  {
    have inb := congr_arg
      (λ z, symbol.nonterminal (lift_rule_ (option.some ∘ sum.inl) ror).input_string.secon ∈ z)
      bef,
    apply false_of_true_eq_false,
    convert inb.symm,
    {
      simp,
    },
    rw list.mem_singleton,
    rw symbol.nonterminal.inj_eq,
    change false = (_ = option.none),
    unfold lift_rule_,
    dsimp [prod.secon],
    clear_except,
    norm_num,
  },
  {
    have inb := congr_arg
      (λ z, symbol.nonterminal (lift_rule_ (option.some ∘ sum.inr) ror).input_string.secon ∈ z)
      bef,
    apply false_of_true_eq_false,
    convert inb.symm,
    {
      simp,
    },
    rw list.mem_singleton,
    rw symbol.nonterminal.inj_eq,
    change false = (_ = option.none),
    unfold lift_rule_,
    dsimp [prod.secon],
    clear_except,
    norm_num,
  },
end


private lemma in_union_of_in_L₁ {w : list T} (ass : w ∈ grammar_language g₁) :
  w ∈ grammar_language union_grammar :=
begin
  unfold grammar_language at ass ⊢,
  rw set.mem_set_of_eq at ass ⊢,
  unfold grammar_generates at ass ⊢,
  apply grammar_deri_of_tran_deri,
  {
    use ⟨ ([], none, []), [symbol.nonterminal (some (sum.inl (g₁.initial)))] ⟩,
    split,
    {
      apply list.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  simp,
  have lifted := lift_deri_ lg₁ ass,
  swap, {
    exact g₂,
  },
  change grammar_derives lg₁.g (lift_string_ lg₁.lift_nt [symbol.nonterminal g₁.initial]) (list.map symbol.terminal w),
  have equiv_out : (lift_string_ lg₁.lift_nt (list.map symbol.terminal w)) = (list.map symbol.terminal w),
  {
    unfold lift_string_,
    rw list.map_map,
    refl,
  },
  rw equiv_out at lifted,
  exact lifted,
end

private lemma in_union_of_in_L₂ {w : list T} (ass : w ∈ grammar_language g₂) :
  w ∈ grammar_language union_grammar :=
begin
  unfold grammar_language at ass ⊢,
  rw set.mem_set_of_eq at ass ⊢,
  unfold grammar_generates at ass ⊢,
  apply grammar_deri_of_tran_deri,
  {
    use ⟨ ([], none, []), [symbol.nonterminal (some (sum.inr (g₂.initial)))] ⟩,
    split,
    {
      apply list.mem_cons_of_mem,
      apply list.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  simp,
  have lifted := lift_deri_ lg₂ ass,
  swap, {
    exact g₁,
  },
  change grammar_derives lg₂.g (lift_string_ lg₂.lift_nt [symbol.nonterminal g₂.initial]) (list.map symbol.terminal w),
  have equiv_out : (lift_string_ lg₂.lift_nt (list.map symbol.terminal w)) = (list.map symbol.terminal w),
  {
    unfold lift_string_,
    rw list.map_map,
    refl,
  },
  rw equiv_out at lifted,
  exact lifted,
end

end RE_union_RE_aux


/-- The class of recursively-enumerable languages is closed under union. -/
theorem RE_of_RE_u_RE {T : Type} [decidable_eq T] (L₁ : language T) (L₂ : language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ + L₂)   :=
begin
  rintro ⟨ ⟨ g₁, h₁ ⟩, ⟨ g₂, h₂ ⟩ ⟩,

  unfold is_RE,
  use @union_grammar T _ g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    intros w ass,
    rw language.mem_add,
    rw ← h₁,
    rw ← h₂,
    exact in_L₁_or_L₂_of_in_union ass,
  },
  {
    intros w ass,
    cases ass with case₁ case₂,
    {
      rw ← h₁ at case₁,
      exact in_union_of_in_L₁ case₁,
    },
    {
      rw ← h₂ at case₂,
      exact in_union_of_in_L₂ case₂,
    },
  },
end
