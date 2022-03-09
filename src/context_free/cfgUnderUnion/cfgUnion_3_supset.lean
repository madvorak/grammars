import context_free.cfgUnderUnion.cfgUnion_1_basic

namespace cfg_union

variables {T : Type} {g₁ g₂ : CF_grammar T}

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (option g₁.nt)
| none := none
| (some (sum.inl nonte)) := some nonte
| (some (sum.inr _)) := none

private def oN₂_of_N : (union_grammar g₁ g₂).nt → (option g₂.nt)
| none := none
| (some (sum.inl _)) := none
| (some (sum.inr nonte)) := some nonte

private def sTN₁_of_sTN : symbol T (union_grammar g₁ g₂).nt → option (symbol T g₁.nt)
| (symbol.terminal te) := some (symbol.terminal te)
| (symbol.nonterminal nont) := option.map symbol.nonterminal (oN₁_of_N nont)

private def sTN₂_of_sTN : symbol T (union_grammar g₁ g₂).nt → option (symbol T g₂.nt)
| (symbol.terminal te) := some (symbol.terminal te)
| (symbol.nonterminal nont) := option.map symbol.nonterminal (oN₂_of_N nont)

private def lsTN₁_of_lsTN (lis : list (symbol T (union_grammar g₁ g₂).nt)) :
  list (symbol T g₁.nt) :=
list.filter_map sTN₁_of_sTN lis

private def lsTN₂_of_lsTN (lis : list (symbol T (union_grammar g₁ g₂).nt)) :
  list (symbol T g₂.nt) :=
list.filter_map sTN₂_of_sTN lis

private def rule₁_of_rule (r : (union_grammar g₁ g₂).nt × (list (symbol T (union_grammar g₁ g₂).nt))) :
  option (g₁.nt × list (symbol T g₁.nt)) :=
match oN₁_of_N r.fst with
  | none := none
  | some x := some (x, lsTN₁_of_lsTN r.snd)
end

private def rule₂_of_rule (r : (union_grammar g₁ g₂).nt × (list (symbol T (union_grammar g₁ g₂).nt))) :
  option (g₂.nt × list (symbol T g₂.nt)) :=
match oN₂_of_N r.fst with
  | none := none
  | some x := some (x, lsTN₂_of_lsTN r.snd)
end

private lemma self_of_sTN₁ (symb : symbol T g₁.nt) :
  sTN₁_of_sTN (@sTN_of_sTN₁ _ _ g₂ symb) = symb :=
begin
  cases symb;
  finish,
end

private lemma self_of_sTN₂ (symb : symbol T g₂.nt) :
  sTN₂_of_sTN (@sTN_of_sTN₂ _ g₁ _ symb) = symb :=
begin
  cases symb;
  finish,
end

private lemma self_of_lsTN₁ (stri : list (symbol T g₁.nt)) :
  lsTN₁_of_lsTN (@lsTN_of_lsTN₁ _ _ g₂ stri) = stri :=
begin
  unfold lsTN_of_lsTN₁,
  unfold lsTN₁_of_lsTN,
  rw list.filter_map_map,
  change list.filter_map (λ x, sTN₁_of_sTN (sTN_of_sTN₁ x)) stri = stri,
  convert_to list.filter_map (λ x, some x) stri = stri,
  {
    have equal_functions : (λ (x : symbol T g₁.nt), sTN₁_of_sTN (sTN_of_sTN₁ x)) = (λ x, some x),
    {
      ext1,
      apply self_of_sTN₁,
    },
    rw ← equal_functions,
    apply congr_fun,
    apply congr_arg,
    ext1,
    apply congr_fun,
    refl,
  },
  finish,
end

private lemma self_of_lsTN₂ (stri : list (symbol T g₂.nt)) :
  lsTN₂_of_lsTN (@lsTN_of_lsTN₂ _ g₁ _ stri) = stri :=
begin
  unfold lsTN_of_lsTN₂,
  unfold lsTN₂_of_lsTN,
  rw list.filter_map_map,
  change list.filter_map (λ x, sTN₂_of_sTN (sTN_of_sTN₂ x)) stri = stri,
  convert_to list.filter_map (λ x, some x) stri = stri,
  {
    have equal_functions : (λ (x : symbol T g₂.nt), sTN₂_of_sTN (sTN_of_sTN₂ x)) = (λ x, some x),
    {
      ext1,
      apply self_of_sTN₂,
    },
    rw ← equal_functions,
    apply congr_fun,
    apply congr_arg,
    ext1,
    apply congr_fun,
    refl,
  },
  finish,
end

private lemma self_of_rule₁ (r : g₁.nt × list (symbol T g₁.nt)) :
  rule₁_of_rule (@rule_of_rule₁ _ _ g₂ r) = r :=
begin
  unfold rule_of_rule₁,
  unfold rule₁_of_rule,
  simp,
  unfold oN₁_of_N,
  cases r,
  simp,
  unfold rule₁_of_rule,
  simp,
  rw self_of_lsTN₁,
  refl,
end

private lemma self_of_rule₂ (r : g₂.nt × list (symbol T g₂.nt)) :
  rule₂_of_rule (@rule_of_rule₂ _ g₁ _ r) = r :=
begin
  unfold rule_of_rule₂,
  unfold rule₂_of_rule,
  simp,
  unfold oN₂_of_N,
  cases r,
  simp,
  unfold rule₂_of_rule,
  simp,
  rw self_of_lsTN₂,
  refl,
end

private lemma tran₁_of_tran {input output : list (symbol T (union_grammar g₁ g₂).nt)}
  (h : ∀ letter ∈ input, or
    (∃ t : T, letter = symbol.terminal t)
    (∃ n₁ : g₁.nt, letter = symbol.nonterminal (some (sum.inl n₁)))
  ):
  CF_transforms (union_grammar g₁ g₂) input output →
    CF_transforms g₁ (lsTN₁_of_lsTN input) (lsTN₁_of_lsTN output) ∧
    (∀ letter ∈ output, or
      (∃ t : T, letter = symbol.terminal t)
      (∃ n₁ : g₁.nt, letter = symbol.nonterminal (some (sum.inl n₁)))
    ) :=
begin
  rintro ⟨ orig_rule, orig_in, v, w, hyp_bef, hyp_aft ⟩,

  have rule_from_g₁ : orig_rule ∈ (list.map (@rule_of_rule₁ _ _ g₂) g₁.rules),
  {
    cases orig_in,
    {
      exfalso,
      rw orig_in at hyp_bef,
      dsimp at hyp_bef,
      rw hyp_bef at h,
      specialize h (symbol.nonterminal none),
      finish,
    },
    cases orig_in,
    {
      exfalso,
      rw orig_in at hyp_bef,
      dsimp at hyp_bef,
      rw hyp_bef at h,
      specialize h (symbol.nonterminal none),
      finish,
    },
    change orig_rule ∈ (list.map rule_of_rule₁ g₁.rules ++ list.map rule_of_rule₂ g₂.rules) at orig_in,
    rw list.mem_append at orig_in,
    cases orig_in.symm with orig_in₂ orig_in₁,
    {
      exfalso,
      rw hyp_bef at h,
      specialize h (symbol.nonterminal orig_rule.fst),
      simp at h,
      change orig_rule ∈ list.map (λ r,
          (some (sum.inr (prod.fst r)), lsTN_of_lsTN₂ (prod.snd r))) g₂.rules at orig_in₂,
      finish,
    },
    exact orig_in₁,
  },

  split,
  {
    have back_rule : ∃ r ∈ g₁.rules, rule₁_of_rule orig_rule = some r,
    {
      rw list.mem_map at rule_from_g₁,
      rcases rule_from_g₁ with ⟨ rul, rul_in, rul_eq ⟩,
      have rul₁_eq := congr_arg rule₁_of_rule rul_eq,
      rw self_of_rule₁ at rul₁_eq,
      use rul,
      exact ⟨ rul_in, rul₁_eq.symm ⟩,
    },
    rcases back_rule with ⟨ some_rule, some_in_g₁, back_orig ⟩,
    use some_rule,
    split,
    {
      exact some_in_g₁
    },
    use lsTN₁_of_lsTN v,
    use lsTN₁_of_lsTN w,
    
    rw list.mem_map at rule_from_g₁,
    rcases rule_from_g₁ with ⟨ r₁, -, r₁_eq ⟩,
    have r₁_conversion := congr_arg rule₁_of_rule r₁_eq,
    rw self_of_rule₁ at r₁_conversion,
    rw back_orig at r₁_conversion,
    split,
    {
      have hyp_bef₁ := congr_arg lsTN₁_of_lsTN hyp_bef,
      rw lsTN₁_of_lsTN at hyp_bef₁,
      rw lsTN₁_of_lsTN at hyp_bef₁,
      rw list.filter_map_append at hyp_bef₁,
      rw list.filter_map_append at hyp_bef₁,
      repeat { rw ← lsTN₁_of_lsTN at hyp_bef₁ },
      convert hyp_bef₁,
      rw ← r₁_eq,
      rw rule_of_rule₁,
      dsimp,
      rw (option.some.inj r₁_conversion),
      refl,
    },
    {
      have hyp_aft₁ := congr_arg lsTN₁_of_lsTN hyp_aft,
      rw lsTN₁_of_lsTN at hyp_aft₁,
      rw lsTN₁_of_lsTN at hyp_aft₁,
      rw list.filter_map_append at hyp_aft₁,
      rw list.filter_map_append at hyp_aft₁,
      repeat { rw ← lsTN₁_of_lsTN at hyp_aft₁ },
      convert hyp_aft₁,
      rw ← r₁_eq,
      rw rule_of_rule₁,
      rw self_of_lsTN₁,
      symmetry,
      rw (option.some.inj r₁_conversion),
    },
  },
  {
    change orig_rule ∈ (list.map (λ r,
        (some (sum.inl (prod.fst r)), lsTN_of_lsTN₁ (prod.snd r))) g₁.rules) at rule_from_g₁,
    rw hyp_aft,
    rw hyp_bef at h,
    intros lette lette_in,
    specialize h lette,
    rw list.append_assoc at lette_in,
    rw list.mem_append at lette_in,
    rw list.mem_append at lette_in,
    rw list.append_assoc at h,
    rw list.mem_append at h,
    rw list.mem_append at h,
    cases lette_in,
    {
      exact h (by {
        left,
        exact lette_in,
      }),
    },
    cases lette_in,
    {
      change orig_rule ∈ (list.map (λ (r : g₁.nt × list (symbol T g₁.nt)),
          (some (sum.inl r.fst), lsTN_of_lsTN₁ r.snd)) g₁.rules) at rule_from_g₁,
      rw list.mem_iff_nth_le at rule_from_g₁,
      cases rule_from_g₁ with index rest,
      cases rest with index_small eq_orig_rule,
      rw ← eq_orig_rule at lette_in,
      simp at lette_in,
      unfold lsTN_of_lsTN₁ at lette_in,
      simp at lette_in,
      cases lette_in with a conju,
      cases conju with trash treasure,
      rw ← treasure,
      cases a,
      {
        left,
        use a,
        refl,
      },
      {
        right,
        use a,
        refl,
      },
    },
    {
      exact h (by {
        right,
        right,
        exact lette_in,
      }),
    },
  },
end

private lemma tran₂_of_tran {input output : list (symbol T (union_grammar g₁ g₂).nt)}
  (h : ∀ letter ∈ input, or
    (∃ t : T, letter = symbol.terminal t)
    (∃ n₂ : g₂.nt, letter = symbol.nonterminal (some (sum.inr n₂)))
  ):
  CF_transforms (union_grammar g₁ g₂) input output →
    CF_transforms g₂ (lsTN₂_of_lsTN input) (lsTN₂_of_lsTN output) ∧
    (∀ letter ∈ output, or
      (∃ t : T, letter = symbol.terminal t)
      (∃ n₂ : g₂.nt, letter = symbol.nonterminal (some (sum.inr n₂)))
    ) :=
begin
  rintro ⟨ orig_rule, orig_in, v, w, hyp_bef, hyp_aft ⟩,

  have rule_from_g₂ : orig_rule ∈ (list.map (@rule_of_rule₂ _ g₁ _) g₂.rules),
  {
    cases orig_in,
    {
      exfalso,
      rw orig_in at hyp_bef,
      dsimp at hyp_bef,
      rw hyp_bef at h,
      specialize h (symbol.nonterminal none),
      finish,
    },
    cases orig_in,
    {
      exfalso,
      rw orig_in at hyp_bef,
      dsimp at hyp_bef,
      rw hyp_bef at h,
      specialize h (symbol.nonterminal none),
      finish,
    },
    change orig_rule ∈ (list.map rule_of_rule₁ g₁.rules ++ list.map rule_of_rule₂ g₂.rules) at orig_in,
    rw list.mem_append at orig_in,
    cases orig_in with orig_in₁ orig_in₂,
    {
      exfalso,
      rw hyp_bef at h,
      specialize h (symbol.nonterminal orig_rule.fst),
      simp at h,
      change orig_rule ∈ list.map (λ r,
          (some (sum.inl (prod.fst r)), lsTN_of_lsTN₁ (prod.snd r))) g₁.rules at orig_in₁,
      finish,
    },
    exact orig_in₂,
  },

  split,
  {
    have back_rule : ∃ r ∈ g₂.rules, rule₂_of_rule orig_rule = some r,
    {
      rw list.mem_map at rule_from_g₂,
      rcases rule_from_g₂ with ⟨ rul, rul_in, rul_eq ⟩,
      have rul₂_eq := congr_arg rule₂_of_rule rul_eq,
      rw self_of_rule₂ at rul₂_eq,
      use rul,
      exact ⟨ rul_in, rul₂_eq.symm ⟩,
    },
    rcases back_rule with ⟨ some_rule, some_in_g₂, back_orig ⟩,
    use some_rule,
    split,
    {
      exact some_in_g₂,
    },
    use lsTN₂_of_lsTN v,
    use lsTN₂_of_lsTN w,
    
    rw list.mem_map at rule_from_g₂,
    rcases rule_from_g₂ with ⟨ r₂, -, r₂_eq ⟩,
    have r₂_conversion := congr_arg rule₂_of_rule r₂_eq,
    rw self_of_rule₂ at r₂_conversion,
    rw back_orig at r₂_conversion,
    split,
    {
      have hyp_bef₂ := congr_arg lsTN₂_of_lsTN hyp_bef,
      rw lsTN₂_of_lsTN at hyp_bef₂,
      rw lsTN₂_of_lsTN at hyp_bef₂,
      rw list.filter_map_append at hyp_bef₂,
      rw list.filter_map_append at hyp_bef₂,
      repeat { rw ← lsTN₂_of_lsTN at hyp_bef₂ },
      convert hyp_bef₂,
      rw ← r₂_eq,
      rw rule_of_rule₂,
      dsimp,
      rw (option.some.inj r₂_conversion),
      refl,
    },
    {
      have hyp_aft₂ := congr_arg lsTN₂_of_lsTN hyp_aft,
      rw lsTN₂_of_lsTN at hyp_aft₂,
      rw lsTN₂_of_lsTN at hyp_aft₂,
      rw list.filter_map_append at hyp_aft₂,
      rw list.filter_map_append at hyp_aft₂,
      repeat { rw ← lsTN₂_of_lsTN at hyp_aft₂ },
      convert hyp_aft₂,
      rw ← r₂_eq,
      rw rule_of_rule₂,
      rw self_of_lsTN₂,
      symmetry,
      rw (option.some.inj r₂_conversion),
    },
  },
  {
    change orig_rule ∈ (list.map (λ r,
        (some (sum.inr (prod.fst r)), lsTN_of_lsTN₂ (prod.snd r))) g₂.rules) at rule_from_g₂,
    rw hyp_aft,
    rw hyp_bef at h,
    intros lette lette_in,
    specialize h lette,
    rw list.append_assoc at lette_in,
    rw list.mem_append at lette_in,
    rw list.mem_append at lette_in,
    rw list.append_assoc at h,
    rw list.mem_append at h,
    rw list.mem_append at h,
    cases lette_in,
    {
      exact h (by {
        left,
        exact lette_in,
      }),
    },
    cases lette_in,
    {
      change orig_rule ∈ (list.map (λ (r : g₂.nt × list (symbol T g₂.nt)),
          (some (sum.inr r.fst), lsTN_of_lsTN₂ r.snd)) g₂.rules) at rule_from_g₂,
      rw list.mem_iff_nth_le at rule_from_g₂,
      cases rule_from_g₂ with index rest,
      cases rest with index_small eq_orig_rule,
      rw ← eq_orig_rule at lette_in,
      simp at lette_in,
      unfold lsTN_of_lsTN₂ at lette_in,
      simp at lette_in,
      cases lette_in with a conju,
      cases conju with trash treasure,
      rw ← treasure,
      cases a,
      {
        left,
        use a,
        refl,
      },
      {
        right,
        use a,
        refl,
      },
    },
    {
      exact h (by {
        right,
        right,
        exact lette_in,
      }),
    },
  },
end

private lemma deri₁_of_deri (output : list (symbol T (union_grammar g₁ g₂).nt)) :
  CF_derives (union_grammar g₁ g₂) [symbol.nonterminal (some (sum.inl g₁.initial))] output →
    CF_derives g₁ [symbol.nonterminal g₁.initial] (lsTN₁_of_lsTN output) ∧
    (∀ letter ∈ output, or
      (∃ t : T, letter = symbol.terminal t)
      (∃ n₁ : g₁.nt, letter = symbol.nonterminal (some (sum.inl n₁)))
    ) :=
begin
  intro h,
  induction h with b c irr orig ih,
  {
    split,
    {
      apply CF_deri_self,
    },
    {
      intros lette lette_in,
      right,
      use g₁.initial,
      rw list.mem_singleton.mp lette_in,
    },
  },
  have transla := tran₁_of_tran ih.right orig,
  split,
  {
    exact CF_deri_of_deri_tran ih.left transla.left,
  },
  {
    exact transla.right,
  },
end

private lemma deri₂_of_deri (output : list (symbol T (union_grammar g₁ g₂).nt)) :
  CF_derives (union_grammar g₁ g₂) [symbol.nonterminal (some (sum.inr g₂.initial))] output →
    CF_derives g₂ [symbol.nonterminal g₂.initial] (lsTN₂_of_lsTN output) ∧
    (∀ letter ∈ output, or
      (∃ t : T, letter = symbol.terminal t)
      (∃ n₂ : g₂.nt, letter = symbol.nonterminal (some (sum.inr n₂)))
    ) :=
begin
  intro h,
  induction h with b c irr orig ih,
  {
    split,
    {
      apply CF_deri_self,
    },
    {
      intros lette lette_in,
      right,
      use g₂.initial,
      rw list.mem_singleton.mp lette_in,
    },
  },
  have transla := tran₂_of_tran ih.right orig,
  split,
  {
    exact CF_deri_of_deri_tran ih.left transla.left,
  },
  {
    exact transla.right,
  },
end

private lemma deri_bridge₁ (output : list (symbol T g₁.nt)) :
  CF_derives (union_grammar g₁ g₂) [symbol.nonterminal (some (sum.inl g₁.initial))] (lsTN_of_lsTN₁ output) →
    CF_derives g₁ [symbol.nonterminal g₁.initial] output :=
begin
  intro h,
  have almost := deri₁_of_deri (lsTN_of_lsTN₁ output) h,
  rw self_of_lsTN₁ at almost,
  exact almost.left,
end

private lemma deri_bridge₂ (output : list (symbol T g₂.nt)) :
  CF_derives (union_grammar g₁ g₂) [symbol.nonterminal (some (sum.inr g₂.initial))] (lsTN_of_lsTN₂ output) →
    CF_derives g₂ [symbol.nonterminal g₂.initial] output :=
begin
  intro h,
  have almost := deri₂_of_deri (lsTN_of_lsTN₂ output) h,
  rw self_of_lsTN₂ at almost,
  exact almost.left,
end

private lemma in_language_left_case_of_union (w : list T)
  (hypo : CF_derives (union_grammar g₁ g₂)
    [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w)) :
  w ∈ CF_language g₁ :=
begin
  unfold CF_language,
  change CF_generates_str g₁ (list.map symbol.terminal w),
  unfold CF_generates_str,
  apply deri_bridge₁,
  convert hypo,
  unfold lsTN_of_lsTN₁,
  finish,
end

private lemma in_language_right_case_of_union (w : list T)
  (hypo : CF_derives (union_grammar g₁ g₂)
    [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal w)) :
  w ∈ CF_language g₂ :=
begin
  unfold CF_language,
  change CF_generates_str g₂ (list.map symbol.terminal w),
  unfold CF_generates_str,
  apply deri_bridge₂,
  convert hypo,
  unfold lsTN_of_lsTN₂,
  finish,
end

private lemma both_empty (u v: list (symbol T (union_grammar g₁ g₂).nt))
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

private lemma in_language_impossible_case_of_union (w : list T)
  (rule : (union_grammar g₁ g₂).nt × list (symbol T (union_grammar g₁ g₂).nt))
  (u v: list (symbol T (union_grammar g₁ g₂).nt)) (hu : u = []) (hv : v = [])
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

lemma in_language_of_in_union (w : list T) :
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

end cfg_union
