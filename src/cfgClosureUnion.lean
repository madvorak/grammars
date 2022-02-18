import cfgClosure

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

/-
--private lemma deri_start (g: CF_grammar T) (g₁: CF_grammar T) : CF_derives g [(@symbol.nonterminal T (option (N₁ ⊕ N₂)) none)] [(@symbol.nonterminal T (option (N₁ ⊕ N₂)) (symbol.nonterminal (some (sum.inl g₁.initial))))] :=
private lemma deri_start (g: CF_grammar T) (gntt : g.nt = (option (N₁ ⊕ N₂))) (g₁: CF_grammar T) (g₁ntt : g.nt = N₁) :
  CF_derives g [(@symbol.nonterminal T g.nt/-(option (N₁ ⊕ N₂))-/ none)] [/-(@symbol.nonterminal T g.nt (symbol.nonterminal (some (sum.inl g₁.initial))))-/] :=
begin

  sorry,
end
-/

theorem CF_under_union_modular {T : Type} (L₁ : language T) (L₂ : language T) :
  ((is_CF L₁) ∧ (is_CF L₂))  →  (is_CF (L₁ + L₂)) :=
begin
  intro input,
  cases input with cf₁ cf₂,

  cases cf₁ with g₁ h₁,
  cases cf₂ with g₂ h₂,

  let N₁ : Type := g₁.nt,
  let N₂ : Type := g₂.nt,
  let N : Type := option (N₁ ⊕ N₂),

  let rules₁ : list (N × (list (symbol T N))) :=
    list.map convert_rule₁_rule g₁.rules,
  let rules₂ : list (N × (list (symbol T N))) :=
    list.map convert_rule₂_rule g₂.rules,
  
  let g := CF_grammar.mk N none (
    (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
    (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
    (rules₁ ++ rules₂)
  ),
  use g,

  apply set.eq_of_subset_of_subset,
  {
    sorry,
  },

  
  -- prove `L₁ + L₂ ⊆ CF_language g`
  intros w h,
  rw language.mem_add at h,
  cases h with case₁ case₂,
  {
    have deri_start : CF_derives g [symbol.nonterminal none] [symbol.nonterminal (some (sum.inl g₁.initial))],
    {
      fconstructor,
        exact [symbol.nonterminal none],
      refl,
      use (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]),
      split,
        finish,
      use [[], []],
      simp,
    },
/-
    have deri_rest : CF_derives g [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w),
    {
      have deri_orig : CF_derives g₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal w),
      {
        finish,
      },
      dsimp at *,
      have deri_step : ∀ input output : list (symbol T N₁),
                        CF_transforms g₁ input output →
                        CF_transforms g (convert_lsTN₁_lsTN input) (convert_lsTN₁_lsTN output),
      {
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
            (list.map convert_rule₁_rule g₁.rules) ++ rules₂),
          have isthere : convert_rule₁_rule rul ∈ list.map convert_rule₁_rule g₁.rules :=
            list.mem_map_of_mem convert_rule₁_rule bel,
          {
            finish,
          },
          exact T,
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
      },
      have deri_more : ∀ input output : list (symbol T N₁),
                         CF_derives g₁ input output →
                         CF_derives g (convert_lsTN₁_lsTN input) (convert_lsTN₁_lsTN output),
      {
        intros inp outp ass,
        induction ass with u v ih₁ orig ih,
        {
          apply CF_derives_reflexive,
        },
        apply @trans _ (CF_derives g) (is_trans.mk relation.transitive_refl_trans_gen),
          finish,
        fconstructor,
          exact (convert_lsTN₁_lsTN u),
        refl,
        exact deri_step u v orig,
      },
      have beginning : [symbol.nonterminal (some (sum.inl g₁.initial))]
                       = convert_lsTN₁_lsTN [symbol.nonterminal g₁.initial],
      {
        finish,
      },
      have ending : (list.map symbol.terminal w)
                    = convert_lsTN₁_lsTN (list.map symbol.terminal w),
      {
        ext1,
        simp,
      },
      rw beginning,
      rw ending,
      exact deri_more [symbol.nonterminal g₁.initial] (list.map symbol.terminal w) deri_orig,
    },

    unfold CF_language,
    change CF_generates_str g (list.map symbol.terminal w),
    unfold CF_generates_str,
    unfold CF_derives,
    apply @trans _ (CF_derives g) (is_trans.mk relation.transitive_refl_trans_gen),
      finish, -- uses `deri_start` here
    exact deri_rest,
  },

  {
    have deri_start : CF_derives g [symbol.nonterminal none] [symbol.nonterminal (some (sum.inr g₂.initial))],
    {
      fconstructor,
        exact [symbol.nonterminal none],
      refl,
      use (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]),
      split,
        finish,
      use [[], []],
      simp,
    },

    have deri_rest : CF_derives g [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal w),
    {
      have deri_orig : CF_derives g₂ [symbol.nonterminal g₂.initial] (list.map symbol.terminal w),
      {
        finish,
      },
      dsimp at *,
      have deri_step : ∀ input output : list (symbol T N₂),
                        CF_transforms g₂ input output →
                        CF_transforms g (convert_lsTN₂_lsTN input) (convert_lsTN₂_lsTN output),
      {
        intros inpu outpu ass,
        cases ass with rul foo,
        cases foo with bel bar,
        cases bar with v baz,
        cases baz with w hyp,
        cases hyp with befo afte,

        use convert_rule₂_rule rul,
        split,
        {
          change convert_rule₂_rule rul ∈ (
            (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
            (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
            rules₁ ++ (list.map convert_rule₂_rule g₂.rules)),
          have isthere : convert_rule₂_rule rul ∈ list.map convert_rule₂_rule g₂.rules :=
            list.mem_map_of_mem convert_rule₂_rule bel,
          finish,
        },
        use convert_lsTN₂_lsTN v,
        use convert_lsTN₂_lsTN w,
        split,
        {
          rw congr_arg convert_lsTN₂_lsTN befo,
          apply list_three_parts,
        },
        {
          change convert_lsTN₂_lsTN outpu = convert_lsTN₂_lsTN v ++ convert_lsTN₂_lsTN rul.snd ++ convert_lsTN₂_lsTN w,
          rw congr_arg convert_lsTN₂_lsTN afte,
          apply list_three_parts,
        },
      },
      have deri_more : ∀ input output : list (symbol T N₂),
                         CF_derives g₂ input output →
                         CF_derives g (convert_lsTN₂_lsTN input) (convert_lsTN₂_lsTN output),
      {
        intros inp outp ass,
        induction ass with u v ih₂ orig ih,
        {
          apply CF_derives_reflexive,
        },
        apply @trans _ (CF_derives g) (is_trans.mk relation.transitive_refl_trans_gen),
          finish,
        fconstructor,
          exact (convert_lsTN₂_lsTN u),
        refl,
        exact deri_step u v orig,
      },
      have beginning : [symbol.nonterminal (some (sum.inr g₂.initial))]
                       = convert_lsTN₂_lsTN [symbol.nonterminal g₂.initial],
      {
        finish,
      },
      have ending : (list.map symbol.terminal w)
                    = convert_lsTN₂_lsTN (list.map symbol.terminal w),
      {
        ext1,
        simp,
      },
      rw beginning,
      rw ending,
      exact deri_more [symbol.nonterminal g₂.initial] (list.map symbol.terminal w) deri_orig,
    },

    unfold CF_language,
    change CF_generates_str g (list.map symbol.terminal w),
    unfold CF_generates_str,
    unfold CF_derives,
    apply @trans _ (CF_derives g) (is_trans.mk relation.transitive_refl_trans_gen),
      finish, -- uses `deri_start` here
    exact deri_rest,
-/
  sorry,
  },
  sorry,
end
