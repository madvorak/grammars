import context_free.cfgUnderUnion.cfgUnion_1_basic

namespace cfg_union

variables {T : Type} {g₁ g₂ : CF_grammar T}

private lemma deri₁_step : ∀ input output : list (symbol T g₁.nt),
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

private lemma deri₂_step : ∀ input output : list (symbol T g₂.nt),
  CF_transforms g₂ input output →
    CF_transforms (union_grammar g₁ g₂) (lsTN_of_lsTN₂ input) (lsTN_of_lsTN₂ output) :=
begin
  intros inpu outpu ass,
  cases ass with rul foo,
  cases foo with bel bar,
  cases bar with v baz,
  cases baz with w hyp,
  cases hyp with befo afte,

  use rule_of_rule₂ rul,
  split,
  {
    change rule_of_rule₂ rul ∈ (
      (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
      (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
      ((list.map rule_of_rule₁ g₁.rules) ++ (list.map rule_of_rule₂ g₂.rules))
    ),
    have isthere : rule_of_rule₂ rul ∈ list.map rule_of_rule₂ g₂.rules :=
      list.mem_map_of_mem rule_of_rule₂ bel,
    {
      finish,
    },
    exact g₁,
  },

  use lsTN_of_lsTN₂ v,
  use lsTN_of_lsTN₂ w,
  split,
  {
    rw congr_arg lsTN_of_lsTN₂ befo,
    apply list_three_parts,
  },
  {
    change lsTN_of_lsTN₂ outpu = lsTN_of_lsTN₂ v ++ lsTN_of_lsTN₂ rul.snd ++ lsTN_of_lsTN₂ w,
    rw congr_arg lsTN_of_lsTN₂ afte,
    apply list_three_parts,
  },
end

private lemma deri₁_more : ∀ output : list (symbol T g₁.nt),
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
    exact ih,
  },
  apply CF_deri_of_tran,
  exact deri₁_step u v orig,
end

private lemma deri₂_more : ∀ output : list (symbol T g₂.nt),
  CF_derives g₂ [symbol.nonterminal g₂.initial] output →
    CF_derives (union_grammar g₁ g₂) (lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial]) (lsTN_of_lsTN₂ output) :=
begin
  intros outp ass,
  induction ass with u v ih₂ orig ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_deri,
  {
    exact ih,
  },
  apply CF_deri_of_tran,
  exact deri₂_step u v orig,
end

lemma in_union_of_in_first (w : list T) :
  w ∈ CF_language g₁  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
begin
  intro assum,

  have deri_start : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal none] [symbol.nonterminal (some (sum.inl g₁.initial))],
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

  have deri_rest : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w),
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

lemma in_union_of_in_second (w : list T) :
  w ∈ CF_language g₂  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
begin
  intro assum,

  have deri_start : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal none] [symbol.nonterminal (some (sum.inr g₂.initial))],
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

  have deri_rest : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal (some (sum.inr g₂.initial))] (list.map symbol.terminal w),
  {
    have beginning : [symbol.nonterminal (some (sum.inr g₂.initial))]
                      = lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial],
    {
      unfold lsTN_of_lsTN₂,
      change [symbol.nonterminal (some (sum.inr g₂.initial))] = [sTN_of_sTN₂ (symbol.nonterminal g₂.initial)],
      unfold sTN_of_sTN₂,
    },
    have ending : (list.map symbol.terminal w)
                  = lsTN_of_lsTN₂ (list.map symbol.terminal w),
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

end cfg_union
