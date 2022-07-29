import context_free.cfg


variables {T : Type}

def lift_symbol {N₀ N : Type} (lift_N : N₀ → N) : symbol T N₀ → symbol T N
| (symbol.terminal ter) := symbol.terminal ter
| (symbol.nonterminal nonter) := symbol.nonterminal (lift_N nonter)

def sink_symbol {N₀ N : Type} (sink_N : N → option N₀) : symbol T N → option (symbol T N₀)
| (symbol.terminal ter) := some (symbol.terminal ter)
| (symbol.nonterminal nonter) := option.map symbol.nonterminal (sink_N nonter)

def lift_string {N₀ N : Type} (lift_N : N₀ → N) :
  list (symbol T N₀) → list (symbol T N) :=
list.map (lift_symbol lift_N)

def sink_string {N₀ N : Type} (sink_N : N → option N₀) :
  list (symbol T N) → list (symbol T N₀) :=
list.filter_map (sink_symbol sink_N)

def lift_rule {N₀ N : Type} (lift_N : N₀ → N) :
  N₀ × (list (symbol T N₀)) → N × (list (symbol T N)) :=
λ r, (lift_N r.fst, lift_string lift_N r.snd)

structure lifted_grammar :=
(g₀ g : CF_grammar T)
(lift_nt : g₀.nt → g.nt)
(lift_inj : function.injective lift_nt)
(corresponding_rules : ∀ r : g₀.nt × list (symbol T g₀.nt),
  r ∈ g₀.rules →
    lift_rule lift_nt r ∈ g.rules
)
(preimage_of_rules : ∀ r : g.nt × list (symbol T g.nt),
  (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, lift_nt n₀ = r.fst) →
    (∃ r₀ ∈ g₀.rules, lift_rule lift_nt r₀ = r)
)
(sink_nt : g.nt → option g₀.nt)
(sink_inj : ∀ x y, sink_nt x = sink_nt y →
  x = y  ∨  sink_nt x = none
)
(lift_nt_sink : ∀ n₀ : g₀.nt, sink_nt (lift_nt n₀) = some n₀)

private lemma lifted_grammar_inverse (lg : @lifted_grammar T) :
  ∀ x : lg.g.nt,
    (∃ val, lg.sink_nt x = some val) →
      option.map lg.lift_nt (lg.sink_nt x) = x :=
begin
  intros x h,
  cases h with valu ass,
  rw ass,
  rw option.map_some',
  apply congr_arg,
  symmetry,
  by_contradiction,
  have inje := lg.sink_inj x (lg.lift_nt valu),
  rw lg.lift_nt_sink at inje,
  cases inje ass with case_valu case_none,
  {
    exact h case_valu,
  },
  rw ass at case_none,
  tauto,
end


private lemma lift_tran
    (lg : lifted_grammar)
    (input output : list (symbol T lg.g₀.nt))
    (hyp : CF_transforms lg.g₀ input output) :
  CF_transforms lg.g (lift_string lg.lift_nt input) (lift_string lg.lift_nt output) :=
begin
  rcases hyp with ⟨rule, rule_in, v, w, bef, aft⟩,
  use lift_rule lg.lift_nt rule,
  split,
  {
    exact lg.corresponding_rules rule rule_in,
  },
  use lift_string lg.lift_nt v,
  use lift_string lg.lift_nt w,
  split,
  {
    have lift_bef := congr_arg (lift_string lg.lift_nt) bef,
    unfold lift_string at *,
    rw list.map_append_append at lift_bef,
    convert lift_bef,
  },
  {
    have lift_aft := congr_arg (lift_string lg.lift_nt) aft,
    unfold lift_string at *,
    rw list.map_append_append at lift_aft,
    exact lift_aft,
  },
end

lemma lift_deri
    (lg : lifted_grammar)
    (input output : list (symbol T lg.g₀.nt))
    (hyp : CF_derives lg.g₀ input output) :
  CF_derives lg.g (lift_string lg.lift_nt input) (lift_string lg.lift_nt output) :=
begin
  induction hyp with u v trash orig ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  exact lift_tran lg u v orig,
end


def good_letter {lg : @lifted_grammar T} : symbol T lg.g.nt → Prop
| (symbol.terminal t)     := true
| (symbol.nonterminal nt) := ∃ n₀ : lg.g₀.nt, lg.sink_nt nt = n₀

def good_string {lg : @lifted_grammar T} (str : list (symbol T lg.g.nt)) :=
∀ letter ∈ str, good_letter letter

private lemma sink_tran
    (lg : lifted_grammar)
    (input output : list (symbol T lg.g.nt))
    (hyp : CF_transforms lg.g input output)
    (ok_input : good_string input) :
  CF_transforms lg.g₀ (sink_string lg.sink_nt input) (sink_string lg.sink_nt output) :=
begin
  rcases hyp with ⟨rule, rule_in, v, w, bef, aft⟩,

  rcases lg.preimage_of_rules rule (by {
    split,
    {
      exact rule_in,
    },
    rw bef at ok_input,
    have good_matched_nonterminal : good_letter (symbol.nonterminal rule.fst),
    {
      specialize ok_input (symbol.nonterminal rule.fst),
      finish,
    },
    change ∃ n₀ : lg.g₀.nt, lg.sink_nt rule.fst = some n₀ at good_matched_nonterminal,
    cases good_matched_nonterminal with n₀ hn₀,
    use n₀,
    have almost := congr_arg (option.map lg.lift_nt) hn₀,
    rw lifted_grammar_inverse lg rule.fst ⟨n₀, hn₀⟩ at almost,
    simp at almost,
    apply option.some_injective,
    exact almost.symm,
  }) with ⟨pre_rule, pre_in, preimage⟩,

  use pre_rule,
  split,
  {
    exact pre_in,
  },
  use sink_string lg.sink_nt v,
  use sink_string lg.sink_nt w,
  have correct_inverse : sink_symbol lg.sink_nt ∘ lift_symbol lg.lift_nt = option.some,
  {
    ext1,
    cases x,
    {
      refl,
    },
    dsimp,
    unfold lift_symbol,
    unfold sink_symbol,
    rw lg.lift_nt_sink,
    apply option.map_some',
  },
  split,
  {
    have sink_bef := congr_arg (sink_string lg.sink_nt) bef,
    unfold sink_string at *,
    rw list.filter_map_append_append at sink_bef,
    convert sink_bef,
    rw ← preimage,
    unfold lift_rule,
    dsimp,
    change
      [symbol.nonterminal pre_rule.fst] =
      list.filter_map (sink_symbol lg.sink_nt)
        (list.map (lift_symbol lg.lift_nt) [symbol.nonterminal pre_rule.fst]),
    rw list.filter_map_map,
    rw correct_inverse,
    rw list.filter_map_some,
  },
  {
    have sink_aft := congr_arg (sink_string lg.sink_nt) aft,
    unfold sink_string at *,
    rw list.filter_map_append_append at sink_aft,
    convert sink_aft,
    rw ← preimage,
    unfold lift_rule,
    dsimp,
    unfold lift_string,
    rw list.filter_map_map,
    rw correct_inverse,
    rw list.filter_map_some,
  },
end

lemma sink_deri
    (lg : lifted_grammar)
    (input output : list (symbol T lg.g.nt))
    (hyp : CF_derives lg.g input output)
    (ok_input : good_string input) :
  CF_derives lg.g₀ (sink_string lg.sink_nt input) (sink_string lg.sink_nt output)
  ∧ good_string output :=
begin
  induction hyp with u v trash orig ih,
  {
    split,
    {
      apply CF_deri_self,
    },
    {
      exact ok_input,
    },
  },
  split,
  {
    apply CF_deri_of_deri_tran,
    {
      exact ih.left,
    },
    exact sink_tran lg u v orig ih.right,
  },
  {
    intros letter in_v,
    have ihr := ih.right letter,
    rcases orig with ⟨rule, in_rules, w₁, w₂, bef, aft⟩,
    rw bef at ihr,
    rw list.mem_append at ihr,
    rw aft at in_v,
    rw list.mem_append at in_v,
    cases in_v,
    rw list.mem_append at in_v,
    cases in_v,
    {
      apply ihr,
      rw list.mem_append,
      left,
      left,
      exact in_v,
    },
    {
      have exn₀ : ∃ (n₀ : lg.g₀.nt), lg.lift_nt n₀ = rule.fst,
      {
        by_cases lg.sink_nt rule.fst = none,
        {
          exfalso,
          have ruu : symbol.nonterminal rule.fst ∈ u,
          {
            rw bef,
            rw list.mem_append,
            left,
            rw list.mem_append,
            right,
            apply list.mem_cons_self,
          },
          have glruf : good_letter (symbol.nonterminal rule.fst),
          {
            exact ih.right (symbol.nonterminal rule.fst) ruu,
          },
          unfold good_letter at glruf,
          rw h at glruf,
          tauto,
        },
        cases (option.ne_none_iff_exists'.mp h) with x ex,
        use x,
        have gix := lifted_grammar_inverse lg rule.fst ⟨x, ex⟩,
        rw ex at gix,
        rw option.map_some' at gix,
        apply option.some_injective,
        exact gix,
      },
      rcases lg.preimage_of_rules rule ⟨in_rules, exn₀⟩ with ⟨rul, in0, lif⟩,
      rw ← lif at in_v,
      unfold lift_rule at in_v,
      dsimp at in_v,
      unfold lift_string at in_v,
      rw list.mem_map at in_v,
      rcases in_v with ⟨s, s_in_rulsnd, symbol_letter⟩,
      rw ← symbol_letter,
      cases s,
      {
        tauto,
      },
      unfold lift_symbol,
      unfold good_letter,
      use s,
      exact lg.lift_nt_sink s,
    },
    {
      apply ihr,
      right,
      exact in_v,
    },
  },
end


meta def five_steps : tactic unit := `[
  apply congr_fun,
  apply congr_arg,
  ext1,
  cases x;
  refl
]


variables {g₁ g₂ : CF_grammar T}

/-- similar to `lift_symbol (option.some ∘ sum.inl)` -/
def sTN_of_sTN₁ : (symbol T g₁.nt) → (symbol T (option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inl snt)))

/-- similar to `lift_symbol (option.some ∘ sum.inr)` -/
def sTN_of_sTN₂ : (symbol T g₂.nt) → (symbol T (option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inr snt)))

/-- similar to `lift_string (option.some ∘ sum.inl)` -/
def lsTN_of_lsTN₁ : list (symbol T g₁.nt) → list (symbol T (option (g₁.nt ⊕ g₂.nt))) :=
list.map sTN_of_sTN₁

/-- similar to `lift_string (option.some ∘ sum.inr)` -/
def lsTN_of_lsTN₂ : list (symbol T g₂.nt) → list (symbol T (option (g₁.nt ⊕ g₂.nt))) :=
list.map sTN_of_sTN₂

/-- similar to `lift_rule (option.some ∘ sum.inl)` -/
def rule_of_rule₁ (r : g₁.nt × (list (symbol T g₁.nt))) :
  ((option (g₁.nt ⊕ g₂.nt)) × (list (symbol T (option (g₁.nt ⊕ g₂.nt))))) :=
(some (sum.inl (prod.fst r)), lsTN_of_lsTN₁ (prod.snd r))

/-- similar to `lift_rule (option.some ∘ sum.inr)` -/
def rule_of_rule₂ (r : g₂.nt × (list (symbol T g₂.nt))) :
  ((option (g₁.nt ⊕ g₂.nt)) × (list (symbol T (option (g₁.nt ⊕ g₂.nt))))) :=
(some (sum.inr (prod.fst r)), lsTN_of_lsTN₂ (prod.snd r))
