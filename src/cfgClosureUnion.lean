import cfg
import tactic


section reusable_lemmata

lemma list_three_parts {T₁ T₂ : Type} {x y z : list T₁} {f : T₁ → T₂} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by simp only [list.map_append]

lemma unpack_transitive_closure {α : Type} {r : α → α → Prop} {x z : α}
  (h : relation.refl_trans_gen r x z) (nontriv : x ≠ z) :
    ∃ y : α, (r x y) ∧ (relation.refl_trans_gen r y z) :=
(relation.refl_trans_gen.cases_head h).resolve_left nontriv

end reusable_lemmata


section specific_defs_and_lemmata
variables {T N₁ N₂ : Type}

private def sTN_of_sTN₁ : (symbol T N₁) → (symbol T (option (N₁ ⊕ N₂)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inl snt)))

private def sTN_of_sTN₂ : (symbol T N₂) → (symbol T (option (N₁ ⊕ N₂)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inr snt)))
/-
private lemma convert_sTN₁_sTN_nn (x : (@symbol T N₁)) : (sTN_of_sTN₁ x) ≠ (@symbol.nonterminal T (option (N₁ ⊕ N₂)) none) :=
begin
  cases x,
  {
    change (symbol.terminal x) ≠ symbol.nonterminal none,
    finish,
  },
  {
    change (symbol.nonterminal (some (sum.inl x))) ≠ symbol.nonterminal none,
    finish,
  },
end

private lemma convert_sTN₂_sTN_nn (x : (@symbol T N₂)) : (sTN_of_sTN₂ x) ≠ (@symbol.nonterminal T (option (N₁ ⊕ N₂)) none) :=
begin
  cases x,
  {
    change (symbol.terminal x) ≠ symbol.nonterminal none,
    finish,
  },
  {
    change (symbol.nonterminal (some (sum.inr x))) ≠ symbol.nonterminal none,
    finish,
  },
end

private lemma convert_sTN₁_sTN_nns (xs : list (@symbol T N₁)) : (@symbol.nonterminal T (option (N₁ ⊕ N₂)) none) ∉ list.map (@sTN_of_sTN₁ T N₁ N₂) xs :=
begin
  norm_num,
  intros x x_in,
  apply convert_sTN₁_sTN_nn,
end

private lemma convert_sTN₂_sTN_nns (xs : list (@symbol T N₂)) : (@symbol.nonterminal T (option (N₁ ⊕ N₂)) none) ∉ list.map (@sTN_of_sTN₂ T N₁ N₂) xs :=
begin
  norm_num,
  intros x x_in,
  apply convert_sTN₂_sTN_nn,
end
-/
private def lsTN_of_lsTN₁ : list (symbol T N₁) → list (symbol T (option (N₁ ⊕ N₂))) :=
list.map sTN_of_sTN₁

private def lsTN_of_lsTN₂ : list (symbol T N₂) → list (symbol T (option (N₁ ⊕ N₂))) :=
list.map sTN_of_sTN₂

private def rule_of_rule₁ (r : N₁ × (list (symbol T N₁))) : ((option (N₁ ⊕ N₂)) × (list (symbol T (option (N₁ ⊕ N₂))))) :=
(some (sum.inl (prod.fst r)), lsTN_of_lsTN₁ (prod.snd r))

private def rule_of_rule₂ (r : N₂ × (list (symbol T N₂))) : ((option (N₁ ⊕ N₂)) × (list (symbol T (option (N₁ ⊕ N₂))))) :=
(some (sum.inr (prod.fst r)), lsTN_of_lsTN₂ (prod.snd r))

private def union_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (option (g₁.nt ⊕ g₂.nt)) none (
  (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
  (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
  ((list.map rule_of_rule₁ g₁.rules) ++ (list.map rule_of_rule₂ g₂.rules))
)


section lemmata_subset

private lemma deri_step (g₁ g₂ : CF_grammar T) : ∀ input output : list (symbol T g₁.nt),
  CF_transforms g₁ input output → 
    CF_transforms (union_grammar g₁ g₂) (lsTN_of_lsTN₁ input) (lsTN_of_lsTN₁ output) :=
begin
  intros inpu outpu ass,
  cases ass with rul foo,
  cases foo with bel bar,
  cases bar with v baz,
  cases baz with w hyp,
  cases hyp with befo afte,

  use rule_of_rule₁ rul,
  split,
  {
    change rule_of_rule₁ rul ∈ (
      (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
      (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
      ((list.map rule_of_rule₁ g₁.rules) ++ (list.map rule_of_rule₂ g₂.rules))
    ),
    have isthere : rule_of_rule₁ rul ∈ list.map rule_of_rule₁ g₁.rules :=
      list.mem_map_of_mem rule_of_rule₁ bel,
    {
      finish,
    },
    exact g₂.nt,
  },
  use lsTN_of_lsTN₁ v,
  use lsTN_of_lsTN₁ w,
  split,
  {
    rw congr_arg lsTN_of_lsTN₁ befo,
    apply list_three_parts,
  },
  {
    change lsTN_of_lsTN₁ outpu = lsTN_of_lsTN₁ v ++ lsTN_of_lsTN₁ rul.snd ++ lsTN_of_lsTN₁ w,
    rw congr_arg lsTN_of_lsTN₁ afte,
    apply list_three_parts,
  },
end

private lemma deri_more (g₁ g₂ : CF_grammar T) : ∀ input output : list (symbol T g₁.nt),
  CF_derives g₁ input output →
    CF_derives (union_grammar g₁ g₂) (lsTN_of_lsTN₁ input) (lsTN_of_lsTN₁ output) :=
begin
  intros inp outp ass,
  induction ass with u v ih₁ orig ih,
  {
    apply CF_derives_reflexive,
  },
  apply CF_derives_transitive,
  {
    finish,
  },
  fconstructor,
    exact (lsTN_of_lsTN₁ u),
  {
    refl,
  },
  exact deri_step g₁ g₂ u v orig,
end

private lemma in_union_of_in_first (g₁ g₂ : CF_grammar T) (w : list T) :
  w ∈ CF_language g₁  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
begin
  intro assum,

  have deri_start : CF_derives (union_grammar g₁ g₂) [symbol.nonterminal none] [symbol.nonterminal (some (sum.inl g₁.initial))],
  {
    fconstructor,
      exact [symbol.nonterminal none],
    refl,
    use (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]),
    split,
    {
      change (@option.none (g₁.nt ⊕ g₂.nt), [symbol.nonterminal (some (sum.inl g₁.initial))]) ∈ (
        (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
        (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
        ((list.map rule_of_rule₁ g₁.rules) ++ (list.map rule_of_rule₂ g₂.rules))
      ),
      apply list.mem_cons_self,
    },
    use [[], []],
    simp,
  },

  have deri_rest : CF_derives (union_grammar g₁ g₂) [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w),
  {
    have beginning : [symbol.nonterminal (some (sum.inl g₁.initial))]
                      = lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial],
    {
      unfold lsTN_of_lsTN₁,
      change [symbol.nonterminal (some (sum.inl g₁.initial))] = [sTN_of_sTN₁ (symbol.nonterminal g₁.initial)],
      unfold sTN_of_sTN₁,
    },
    have ending : (list.map symbol.terminal w)
                  = lsTN_of_lsTN₁ (list.map symbol.terminal w),
    {
      ext1,
      unfold lsTN_of_lsTN₁,
      simp,
      apply congr_arg,
      refl,
    },
    rw beginning,
    rw ending,
    exact deri_more g₁ g₂ [symbol.nonterminal g₁.initial] (list.map symbol.terminal w) assum,
  },

  unfold CF_language,
  change CF_generates_str (union_grammar g₁ g₂) (list.map symbol.terminal w),
  unfold CF_generates_str,
  unfold CF_derives,
  apply CF_derives_transitive,
  {
    finish, -- uses `deri_start` here
  },
  exact deri_rest,
end

private lemma in_union_of_in_second (g₁ g₂ : CF_grammar T) (w : list T) :
  w ∈ CF_language g₂  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
begin
  sorry,
end

end lemmata_subset


section lemmata_supset

private lemma both_empty (g₁ g₂ : CF_grammar T)
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

private def sTN₁_of_sTN {g₁ g₂ : CF_grammar T} : symbol T (union_grammar g₁ g₂).nt → option (symbol T g₁.nt)
| (symbol.terminal te) := some (symbol.terminal te)
| (symbol.nonterminal none) := none
| (symbol.nonterminal (some (sum.inl nonte))) := some (symbol.nonterminal nonte)
| (symbol.nonterminal (some (sum.inr _))) := none

private def lsTN₁_of_lsTN {g₁ g₂ : CF_grammar T} (lis : list (symbol T (union_grammar g₁ g₂).nt)) : list (symbol T g₁.nt) :=
list.filter_map sTN₁_of_sTN lis

private lemma self_of_sTN₁ {g₁ g₂ : CF_grammar T} (symb : symbol T g₁.nt) :
  @sTN₁_of_sTN T g₁ g₂ (sTN_of_sTN₁ symb) = symb :=
begin
  cases symb;
  finish,
end

private lemma self_of_lsTN₁ {g₁ g₂ : CF_grammar T} (stri : list (symbol T g₁.nt)) :
  @lsTN₁_of_lsTN T g₁ g₂ (lsTN_of_lsTN₁ stri) = stri :=
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
    finish,
  },
  finish,
end

private def rule₁_of_rule {g₁ g₂ : CF_grammar T} (r : ((union_grammar g₁ g₂).nt × (list (symbol T (union_grammar g₁ g₂).nt)))) : g₁.nt × (list (symbol T g₁.nt)) :=
sorry

private lemma tra₁_of_tra {g₁ g₂ : CF_grammar T} {input output : list (symbol T (union_grammar g₁ g₂).nt)} :
  CF_transforms (union_grammar g₁ g₂) input output →
    CF_transforms g₁ (lsTN₁_of_lsTN input) (lsTN₁_of_lsTN output) :=
begin
  intro h,
  cases h with rule rest,
  cases rest with rule_in foo,
  cases foo with v bar,
  cases bar with w hyp,
  use rule₁_of_rule rule,
  
  sorry,
end

private lemma deri_indu (g₁ g₂ : CF_grammar T) (input output : list (symbol T (union_grammar g₁ g₂).nt)) :
  CF_derives (union_grammar g₁ g₂) input output →
    CF_derives g₁ (lsTN₁_of_lsTN input) (lsTN₁_of_lsTN output) :=
begin
  intro h,
  induction h with b c irr orig ih,
  {
    apply CF_derives_reflexive,
  },
  apply CF_der_of_der_tra,
  {
    exact ih,
  },
  exact tra₁_of_tra orig,
end

private lemma deri_bridge (g₁ g₂ : CF_grammar T) (input output : list (symbol T g₁.nt)) :
  CF_derives (union_grammar g₁ g₂) (lsTN_of_lsTN₁ input) (lsTN_of_lsTN₁ output) →
    CF_derives g₁ input output :=
begin
  intro h,
  have almost := deri_indu g₁ g₂ (lsTN_of_lsTN₁ input) (lsTN_of_lsTN₁ output) h,
  rw self_of_lsTN₁ at almost,
  rw self_of_lsTN₁ at almost,
  exact almost,
end

private lemma in_language_left_case_of_union (g₁ g₂ : CF_grammar T) (w : list T)
  (hypo : CF_derives (union_grammar g₁ g₂)
    [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w)) :
  w ∈ CF_language g₁ :=
begin
  unfold CF_language,
  change CF_generates_str g₁ (list.map symbol.terminal w),
  unfold CF_generates_str,
  apply deri_bridge,
  convert hypo,
  unfold lsTN_of_lsTN₁,
  finish,
end

private lemma in_language_right_case_of_union (g₁ g₂ : CF_grammar T) (w : list T)
  (hypo : relation.refl_trans_gen (CF_transforms (union_grammar g₁ g₂)) -- TODO change type of `hypo`
    [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal w)) :
  w ∈ CF_language g₂ :=
begin

  sorry,
end

private lemma in_language_impossible_case_of_union (g₁ g₂ : CF_grammar T) (w : list T)
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

private lemma in_language_of_in_union (g₁ g₂ : CF_grammar T) (w : list T) :
  w ∈ CF_language (union_grammar g₁ g₂)   →   w ∈ CF_language g₁  ∨  w ∈ CF_language g₂   :=
begin
  intro ass,

  cases unpack_transitive_closure ass begin
    by_contradiction hyp,
    have zeroth := congr_arg (λ p, list.nth p 0) hyp,
    simp at zeroth,
    cases (w.nth 0);
    finish,
  end with S₁ foo,
  cases foo with deri_head deri_tail,

  cases deri_head with rule hhead,
  cases hhead with ruleok h',
  cases h' with u bar,
  cases bar with v baz,
  cases baz with h_bef h_aft,

  rw h_aft at deri_tail,
  cases both_empty g₁ g₂ u v (symbol.nonterminal rule.fst) h_bef with u_nil v_nil,

  cases ruleok with g₁S r_rest,
  {
    left,
    rw g₁S at *,
    simp at *,
    rw u_nil at deri_tail,
    rw v_nil at deri_tail,
    simp at deri_tail,
    exact in_language_left_case_of_union g₁ g₂ w deri_tail,
  },
  cases r_rest with g₂S r_imposs,
  {
    right,
    rw g₂S at *,
    simp at *,
    rw u_nil at deri_tail,
    rw v_nil at deri_tail,
    simp at deri_tail,
    exact in_language_right_case_of_union g₁ g₂ w deri_tail,
  },
  exact in_language_impossible_case_of_union g₁ g₂ w
    rule u v u_nil v_nil h_bef r_imposs,
end

end lemmata_supset


end specific_defs_and_lemmata


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
    exact in_language_of_in_union g₁ g₂ w hyp,
  },
  {
    -- prove `L₁ + L₂ ⊆ `
    intros w hyp,
    rw language.mem_add at hyp,
    cases hyp with case₁ case₂,
    {
      rw ← h₁ at case₁,
      exact in_union_of_in_first g₁ g₂ w case₁,
    },
    {
      rw ← h₂ at case₂,
      exact in_union_of_in_second g₁ g₂ w case₂,
    },
  }
end
