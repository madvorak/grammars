import cfg
import tactic


section reusable_lemmata

lemma list_three_parts {α β : Type} {x y z : list α} {f : α → β} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by simp only [list.map_append]

end reusable_lemmata


section specific_defs_and_lemmata
variables {T : Type} {g₁ g₂ : CF_grammar T}

private def sTN_of_sTN₁ : (symbol T g₁.nt) → (symbol T (option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inl snt)))

private def sTN_of_sTN₂ : (symbol T g₂.nt) → (symbol T (option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inr snt)))

private def lsTN_of_lsTN₁ : list (symbol T g₁.nt) → list (symbol T (option (g₁.nt ⊕ g₂.nt))) :=
list.map sTN_of_sTN₁

private def lsTN_of_lsTN₂ : list (symbol T g₂.nt) → list (symbol T (option (g₁.nt ⊕ g₂.nt))) :=
list.map sTN_of_sTN₂

private def rule_of_rule₁ (r : g₁.nt × (list (symbol T g₁.nt))) :
  ((option (g₁.nt ⊕ g₂.nt)) × (list (symbol T (option (g₁.nt ⊕ g₂.nt))))) :=
(some (sum.inl (prod.fst r)), lsTN_of_lsTN₁ (prod.snd r))

private def rule_of_rule₂ (r : g₂.nt × (list (symbol T g₂.nt))) :
  ((option (g₁.nt ⊕ g₂.nt)) × (list (symbol T (option (g₁.nt ⊕ g₂.nt))))) :=
(some (sum.inr (prod.fst r)), lsTN_of_lsTN₂ (prod.snd r))

private def union_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (option (g₁.nt ⊕ g₂.nt)) none (
  (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
  (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
  ((list.map rule_of_rule₁ g₁.rules) ++ (list.map rule_of_rule₂ g₂.rules))
)


section lemmata_subset

private lemma deri_step : ∀ input output : list (symbol T g₁.nt),
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
    exact g₂,
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

private lemma deri_more : ∀ output : list (symbol T g₁.nt),
  CF_derives g₁ [symbol.nonterminal g₁.initial] output →
    CF_derives (union_grammar g₁ g₂) (lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial]) (lsTN_of_lsTN₁ output) :=
begin
  intros outp ass,
  induction ass with u v ih₁ orig ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_deri,
  {
    finish,
  },
  apply CF_deri_of_tran,
  exact deri_step u v orig,
end

private lemma in_union_of_in_first (w : list T) :
  w ∈ CF_language g₁  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
begin
  intro assum,

  have deri_start : CF_derives (union_grammar g₁ g₂) [symbol.nonterminal none] [symbol.nonterminal (some (sum.inl g₁.initial))],
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
    exact deri_more (list.map symbol.terminal w) assum,
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
  sorry,
end

end lemmata_subset


section lemmata_supset

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

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (option g₁.nt)
| none := none
| (some (sum.inl nonte)) := some nonte
| (some (sum.inr _)) := none

private def sTN₁_of_sTN : symbol T (union_grammar g₁ g₂).nt → option (symbol T g₁.nt)
| (symbol.terminal te) := some (symbol.terminal te)
| (symbol.nonterminal nont) := option.map symbol.nonterminal (oN₁_of_N nont)

private def lsTN₁_of_lsTN (lis : list (symbol T (union_grammar g₁ g₂).nt)) :
  list (symbol T g₁.nt) :=
list.filter_map sTN₁_of_sTN lis

private def rule₁_of_rule (r : (union_grammar g₁ g₂).nt × (list (symbol T (union_grammar g₁ g₂).nt))) :
  option (g₁.nt × list (symbol T g₁.nt)) :=
match oN₁_of_N r.fst with
  | none := none
  | some x := some (x, lsTN₁_of_lsTN r.snd)
end

private lemma self_of_sTN₁ (symb : symbol T g₁.nt) :
  sTN₁_of_sTN (@sTN_of_sTN₁ _ _ g₂ symb) = symb :=
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

private lemma tran₁_of_tran {input output : list (symbol T (union_grammar g₁ g₂).nt)} :
-- here we need an additional assumption
  CF_transforms (union_grammar g₁ g₂) input output →
    CF_transforms g₁ (lsTN₁_of_lsTN input) (lsTN₁_of_lsTN output) :=
begin
  intro h,
  cases h with rule rest,
  cases rest with rule_in foo,
  cases foo with v bar,
  cases bar with w hyp,
  have rule_back : ∃ r : (g₁.nt × list (symbol T g₁.nt)), rule₁_of_rule rule = some r,
  {
    
    sorry,
  },
  cases rule_back with actual_rule rule_corresponds,
  use actual_rule,
  change rule ∈ (
    (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
    (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
    ((list.map rule_of_rule₁ g₁.rules) ++ (list.map rule_of_rule₂ g₂.rules))
  ) at rule_in,
  cases rule_in,
  {
    exfalso,

    sorry,
  },
  cases rule_in,
  {
    exfalso,

    sorry,
  },
  have rule_there : list.mem rule (list.map rule_of_rule₁ g₁.rules),
  {
    
    sorry,
  },
  /-
  have wrapped_rule : list.mem (some rule) (list.map rule₁_of_rule (list.map rule_of_rule₁ g₁.rules)),
  {

    sorry,
  },
  -/
  split,
  {

    sorry,
  },
  use lsTN₁_of_lsTN v,
  use lsTN₁_of_lsTN w,
  cases hyp with hyp_bef hyp_aft,
  split,
  {
    have converted_bef := congr_arg lsTN₁_of_lsTN hyp_bef,
    change list.filter_map sTN₁_of_sTN input = list.filter_map sTN₁_of_sTN (v ++ [symbol.nonterminal rule.fst] ++ w) at converted_bef,
    rw list.filter_map_append at converted_bef,
    rw list.filter_map_append at converted_bef,
    unfold lsTN₁_of_lsTN,
    --have some_bef := congr_arg option.some converted_bef,
    convert converted_bef,
    sorry,
  },
  {
    have converted_aft := congr_arg lsTN₁_of_lsTN hyp_aft,

    sorry,
  },
end

private lemma deri_indu (output : list (symbol T (union_grammar g₁ g₂).nt)) :
  CF_derives (union_grammar g₁ g₂) [symbol.nonterminal (some (sum.inl g₁.initial))] output →
    CF_derives g₁ [symbol.nonterminal g₁.initial] (lsTN₁_of_lsTN output) :=
begin
  intro h,
  induction h with b c irr orig ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  exact tran₁_of_tran orig,
end

private lemma deri_bridge (output : list (symbol T g₁.nt)) :
  CF_derives (union_grammar g₁ g₂) [symbol.nonterminal (some (sum.inl g₁.initial))] (lsTN_of_lsTN₁ output) →
    CF_derives g₁ [symbol.nonterminal g₁.initial] output :=
begin
  intro h,
  have almost := deri_indu (lsTN_of_lsTN₁ output) h,
  rw self_of_lsTN₁ at almost,
  exact almost,
end

private lemma in_language_left_case_of_union (w : list T)
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

private lemma in_language_right_case_of_union (w : list T)
  (hypo : CF_derives (union_grammar g₁ g₂)
    [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal w)) :
  w ∈ CF_language g₂ :=
begin

  sorry,
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

private lemma in_language_of_in_union (w : list T) :
  w ∈ CF_language (union_grammar g₁ g₂)   →   w ∈ CF_language g₁  ∨  w ∈ CF_language g₂   :=
begin
  intro ass,

  cases CF_tran_or_id_of_deri ass with impossible foo,
  {
    exfalso,
    have zeroth := congr_arg (λ p, list.nth p 0) impossible,
    simp at zeroth,
    cases (w.nth 0);
    finish,
  },
  cases foo with S₁ bar,
  cases bar with deri_head deri_tail,

  cases deri_head with rule hhead,
  cases hhead with ruleok h',
  cases h' with u bar,
  cases bar with v baz,
  cases baz with h_bef h_aft,

  rw h_aft at deri_tail,
  cases both_empty u v (symbol.nonterminal rule.fst) h_bef with u_nil v_nil,

  cases ruleok with g₁S r_rest,
  {
    -- will need to somehow propagate information that only symbols from `T` and `N₁` are used inside
    -- probably as a part of induction hypothesis, base step satisfied by `some (sum.inl g₁.initial)`
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
    -- will need to somehow propagate information that only symbols from `T` and `N₂` are used inside
    -- probably as a part of induction hypothesis, base step satisfied by `some (sum.inr g₂.initial)`
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
