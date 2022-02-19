import cfg
import tactic


section reusable_lemmata

lemma CF_derives_reflexive {T : Type} {g : CF_grammar T} {w : list (symbol T g.nt)} :
  CF_derives g w w :=
relation.refl_trans_gen.refl

lemma list_three_parts {T₁ T₂ : Type} {x y z : list T₁} {f : T₁ → T₂} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by simp

lemma unpack_transitive_closure {α : Type} {r : α → α → Prop} {x z : α}
  (h : relation.refl_trans_gen r x z) (nontriv : x ≠ z) :
    ∃ y : α, (r x y) ∧ (relation.refl_trans_gen r y z) :=
(relation.refl_trans_gen.cases_head h).resolve_left nontriv

end reusable_lemmata


section specific_defs_and_lemmata
variables {T N₁ N₂ : Type}

private def convert_sTN₁_sTN : (symbol T N₁) → (symbol T (option (N₁ ⊕ N₂)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inl snt)))

private def convert_sTN₂_sTN : (symbol T N₂) → (symbol T (option (N₁ ⊕ N₂)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inr snt)))

private lemma convert_sTN₁_sTN_nn (x : (@symbol T N₁)) : (convert_sTN₁_sTN x) ≠ (@symbol.nonterminal T (option (N₁ ⊕ N₂)) none) :=
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

private lemma convert_sTN₂_sTN_nn (x : (@symbol T N₂)) : (convert_sTN₂_sTN x) ≠ (@symbol.nonterminal T (option (N₁ ⊕ N₂)) none) :=
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

private lemma convert_sTN₁_sTN_nns (xs : list (@symbol T N₁)) : (@symbol.nonterminal T (option (N₁ ⊕ N₂)) none) ∉ list.map (@convert_sTN₁_sTN T N₁ N₂) xs :=
begin
  norm_num,
  intros x x_in,
  apply convert_sTN₁_sTN_nn,
end

private lemma convert_sTN₂_sTN_nns (xs : list (@symbol T N₂)) : (@symbol.nonterminal T (option (N₁ ⊕ N₂)) none) ∉ list.map (@convert_sTN₂_sTN T N₁ N₂) xs :=
begin
  norm_num,
  intros x x_in,
  apply convert_sTN₂_sTN_nn,
end

private def convert_lsTN₁_lsTN : list (symbol T N₁) → list (symbol T (option (N₁ ⊕ N₂))) :=
list.map convert_sTN₁_sTN

private def convert_lsTN₂_lsTN : list (symbol T N₂) → list (symbol T (option (N₁ ⊕ N₂))) :=
list.map convert_sTN₂_sTN

private def convert_rule₁_rule (r : N₁ × (list (symbol T N₁))) : ((option (N₁ ⊕ N₂)) × (list (symbol T (option (N₁ ⊕ N₂))))) :=
(some (sum.inl (prod.fst r)), convert_lsTN₁_lsTN (prod.snd r))

private def convert_rule₂_rule (r : N₂ × (list (symbol T N₂))) : ((option (N₁ ⊕ N₂)) × (list (symbol T (option (N₁ ⊕ N₂))))) :=
(some (sum.inr (prod.fst r)), convert_lsTN₂_lsTN (prod.snd r))

private def union_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (option (g₁.nt ⊕ g₂.nt)) none (
  (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
  (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
  ((list.map convert_rule₁_rule g₁.rules) ++ (list.map convert_rule₂_rule g₂.rules))
)


section lemmata_subset

private lemma deri_step (g₁ g₂ : CF_grammar T) : ∀ input output : list (symbol T g₁.nt),
  CF_transforms g₁ input output → 
    CF_transforms (union_grammar g₁ g₂) (convert_lsTN₁_lsTN input) (convert_lsTN₁_lsTN output) :=
begin
  intros inpu outpu ass,
  cases ass with rul foo,
  cases foo with bel bar,
  cases bar with v baz,
  cases baz with w hyp,
  cases hyp with befo afte,

  use convert_rule₁_rule rul,
  split,
  {
    change convert_rule₁_rule rul ∈ (
      (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
      (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
      ((list.map convert_rule₁_rule g₁.rules) ++ (list.map convert_rule₂_rule g₂.rules))
    ),
    have isthere : convert_rule₁_rule rul ∈ list.map convert_rule₁_rule g₁.rules :=
      list.mem_map_of_mem convert_rule₁_rule bel,
    {
      finish,
    },
    exact g₂.nt,
  },
  use convert_lsTN₁_lsTN v,
  use convert_lsTN₁_lsTN w,
  split,
  {
    rw congr_arg convert_lsTN₁_lsTN befo,
    apply list_three_parts,
  },
  {
    change convert_lsTN₁_lsTN outpu = convert_lsTN₁_lsTN v ++ convert_lsTN₁_lsTN rul.snd ++ convert_lsTN₁_lsTN w,
    rw congr_arg convert_lsTN₁_lsTN afte,
    apply list_three_parts,
  },
end

private lemma deri_more (g₁ g₂ : CF_grammar T) : ∀ input output : list (symbol T g₁.nt),
  CF_derives g₁ input output →
    CF_derives (union_grammar g₁ g₂) (convert_lsTN₁_lsTN input) (convert_lsTN₁_lsTN output) :=
begin
  intros inp outp ass,
  induction ass with u v ih₁ orig ih,
  {
    apply CF_derives_reflexive,
  },
  apply @trans _ (CF_derives (union_grammar g₁ g₂)) (is_trans.mk relation.transitive_refl_trans_gen),
    finish,
  fconstructor,
    exact (convert_lsTN₁_lsTN u),
  {
    refl,
  },
  exact deri_step g₁ g₂ u v orig,
end

private lemma in_union_of_in_first (g₁ g₂ : CF_grammar T) (w : list T) :
--  (@CF_language T g₁) ⊆ (@CF_language T (union_grammar g₁ g₂)) :=
  w ∈ CF_language g₁ → w ∈ CF_language (union_grammar g₁ g₂) :=
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
        ((list.map convert_rule₁_rule g₁.rules) ++ (list.map convert_rule₂_rule g₂.rules))
      ),
      apply list.mem_cons_self,
    },
    use [[], []],
    simp,
  },

  have deri_rest : CF_derives (union_grammar g₁ g₂) [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w),
  {
    have beginning : [symbol.nonterminal (some (sum.inl g₁.initial))]
                      = convert_lsTN₁_lsTN [symbol.nonterminal g₁.initial],
    {
      unfold convert_lsTN₁_lsTN,
      change [symbol.nonterminal (some (sum.inl g₁.initial))] = [convert_sTN₁_sTN (symbol.nonterminal g₁.initial)],
      unfold convert_sTN₁_sTN,
    },
    have ending : (list.map symbol.terminal w)
                  = convert_lsTN₁_lsTN (list.map symbol.terminal w),
    {
      ext1,
      unfold convert_lsTN₁_lsTN,
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
  apply @trans _ (CF_derives (union_grammar g₁ g₂)) (is_trans.mk relation.transitive_refl_trans_gen),
    finish, -- uses `deri_start` here
  exact deri_rest,
end

private lemma in_union_of_in_second (g₁ g₂ : CF_grammar T) (w : list T) :
  w ∈ CF_language g₂ → w ∈ CF_language (union_grammar g₁ g₂) :=
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

private lemma in_language_left_case_of_union (g₁ g₂ : CF_grammar T) (w : list T)
  (hypo : relation.refl_trans_gen (CF_transforms (union_grammar g₁ g₂))
    [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w)) :
  w ∈ CF_language g₁ :=
begin

  sorry,
end

private lemma in_language_right_case_of_union (g₁ g₂ : CF_grammar T) (w : list T)
  (hypo : relation.refl_trans_gen (CF_transforms (union_grammar g₁ g₂))
    [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal w)) :
  w ∈ CF_language g₂ :=
begin
  
  sorry,
end

private lemma in_language_impossible_case_of_union (g₁ g₂ : CF_grammar T) (w : list T)
  (rule : (union_grammar g₁ g₂).nt × list (symbol T (union_grammar g₁ g₂).nt))
  (u v: list (symbol T (union_grammar g₁ g₂).nt)) (hu : u = []) (hv : v = [])
  (bef: [symbol.nonterminal (union_grammar g₁ g₂).initial] = u ++ [symbol.nonterminal rule.fst] ++ v)
  (sbi : rule ∈ (list.map convert_rule₁_rule g₁.rules ++ list.map convert_rule₂_rule g₂.rules)) :
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
  w ∈ CF_language (union_grammar g₁ g₂) → (w ∈ CF_language g₁ ∨ w ∈ CF_language g₂) :=
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


theorem CF_under_union {T : Type} (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ + L₂) :=
begin
  intro input,
  cases input with cf₁ cf₂,
  cases cf₁ with g₁ h₁,
  cases cf₂ with g₂ h₂,
  
  use union_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    intros w ass,
    simp,
    rw ← h₁,
    rw ← h₂,
    exact in_language_of_in_union g₁ g₂ w ass,
  },
  
  -- prove `L₁ + L₂ ⊆ CF_language g`
  intros w h,
  rw language.mem_add at h,

  cases h with case₁ case₂,
  {
    have cas₁ : w ∈ CF_language g₁,
    {
      rw ← h₁ at case₁,
      exact case₁,
    },
    exact in_union_of_in_first g₁ g₂ w cas₁,
  },
  {
    have cas₂ : w ∈ CF_language g₂,
    {
      rw ← h₂ at case₂,
      exact case₂,
    },
    exact in_union_of_in_second g₁ g₂ w cas₂,
  },
end
