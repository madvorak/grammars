import classes.context_free.basics.toolbox
import utilities.list_utils


variables {T : Type}

def lift_symbol {N₀ N : Type} (lift_N : N₀ → N) : symbol T N₀ → symbol T N
| (symbol.terminal t)    := symbol.terminal t
| (symbol.nonterminal n) := symbol.nonterminal (lift_N n)

def sink_symbol {N₀ N : Type} (sink_N : N → option N₀) : symbol T N → option (symbol T N₀)
| (symbol.terminal t)    := some (symbol.terminal t)
| (symbol.nonterminal n) := option.map symbol.nonterminal (sink_N n)

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
(sink_nt : g.nt → option g₀.nt)
(sink_inj : ∀ x y, sink_nt x = sink_nt y →
  x = y  ∨  sink_nt x = none
)
(preimage_of_rules : ∀ r : g.nt × list (symbol T g.nt),
  (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, lift_nt n₀ = r.fst) →
    (∃ r₀ ∈ g₀.rules, lift_rule lift_nt r₀ = r)
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
  exact option.no_confusion case_none,
end


private lemma lift_tran {lg : lifted_grammar} {w₁ w₂ : list (symbol T lg.g₀.nt)}
    (hyp : CF_transforms lg.g₀ w₁ w₂) :
  CF_transforms lg.g (lift_string lg.lift_nt w₁) (lift_string lg.lift_nt w₂) :=
begin
  rcases hyp with ⟨r, rin, u, v, bef, aft⟩,
  use lift_rule lg.lift_nt r,
  split,
  {
    exact lg.corresponding_rules r rin,
  },
  use lift_string lg.lift_nt u,
  use lift_string lg.lift_nt v,
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

lemma lift_deri {lg : lifted_grammar} {w₁ w₂ : list (symbol T lg.g₀.nt)}
    (hyp : CF_derives lg.g₀ w₁ w₂) :
  CF_derives lg.g (lift_string lg.lift_nt w₁) (lift_string lg.lift_nt w₂) :=
begin
  induction hyp with x y trash orig ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  exact lift_tran orig,
end


def good_letter {lg : @lifted_grammar T} : symbol T lg.g.nt → Prop
| (symbol.terminal t)    := true
| (symbol.nonterminal n) := (∃ n₀ : lg.g₀.nt, lg.sink_nt n = n₀)

def good_string {lg : @lifted_grammar T} (s : list (symbol T lg.g.nt)) :=
∀ a ∈ s, good_letter a

private lemma sink_tran {lg : lifted_grammar} {w₁ w₂ : list (symbol T lg.g.nt)}
    (hyp : CF_transforms lg.g w₁ w₂)
    (ok_input : good_string w₁) :
  CF_transforms lg.g₀ (sink_string lg.sink_nt w₁) (sink_string lg.sink_nt w₂) :=
begin
  rcases hyp with ⟨r, rin, u, v, bef, aft⟩,

  rcases lg.preimage_of_rules r (by {
    split,
    {
      exact rin,
    },
    rw bef at ok_input,
    have good_matched_nonterminal : good_letter (symbol.nonterminal r.fst),
    {
      specialize ok_input (symbol.nonterminal r.fst),
      finish,
    },
    change ∃ n₀ : lg.g₀.nt, lg.sink_nt r.fst = some n₀ at good_matched_nonterminal,
    cases good_matched_nonterminal with n₀ hn₀,
    use n₀,
    have almost := congr_arg (option.map lg.lift_nt) hn₀,
    rw lifted_grammar_inverse lg r.fst ⟨n₀, hn₀⟩ at almost,
    rw option.map_some' at almost,
    apply option.some_injective,
    exact almost.symm,
  }) with ⟨p, pin, preimage⟩,

  use p,
  split,
  {
    exact pin,
  },
  use sink_string lg.sink_nt u,
  use sink_string lg.sink_nt v,
  have correct_inverse : sink_symbol lg.sink_nt ∘ lift_symbol lg.lift_nt = option.some,
  {
    ext1,
    cases x,
    {
      refl,
    },
    rw function.comp_app,
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
    rw ←preimage,
    unfold lift_rule,
    dsimp only,
    change
      [symbol.nonterminal p.fst] =
      list.filter_map (sink_symbol lg.sink_nt)
        (list.map (lift_symbol lg.lift_nt) [symbol.nonterminal p.fst]),
    rw list.filter_map_map,
    rw correct_inverse,
    rw list.filter_map_some,
  },
  {
    have sink_aft := congr_arg (sink_string lg.sink_nt) aft,
    unfold sink_string at *,
    rw list.filter_map_append_append at sink_aft,
    convert sink_aft,
    rw ←preimage,
    unfold lift_rule,
    dsimp only,
    unfold lift_string,
    rw list.filter_map_map,
    rw correct_inverse,
    rw list.filter_map_some,
  },
end

lemma sink_deri (lg : lifted_grammar) (w₁ w₂ : list (symbol T lg.g.nt))
    (hyp : CF_derives lg.g w₁ w₂)
    (ok_input : good_string w₁) :
  CF_derives lg.g₀ (sink_string lg.sink_nt w₁) (sink_string lg.sink_nt w₂)
  ∧ good_string w₂ :=
begin
  induction hyp with x y trash orig ih,
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
    exact sink_tran orig ih.right,
  },
  {
    intros a in_y,
    have ihr := ih.right a,
    rcases orig with ⟨r, in_rules, u, y, bef, aft⟩,
    rw bef at ihr,
    rw list.mem_append at ihr,
    rw aft at in_y,
    rw list.mem_append at in_y,
    cases in_y,
    rw list.mem_append at in_y,
    cases in_y,
    {
      apply ihr,
      rw list.mem_append,
      left,
      left,
      exact in_y,
    },
    {
      have exn₀ : ∃ (n₀ : lg.g₀.nt), lg.lift_nt n₀ = r.fst,
      {
        by_cases lg.sink_nt r.fst = none,
        {
          exfalso,
          have ruu : symbol.nonterminal r.fst ∈ x,
          {
            rw bef,
            rw list.mem_append,
            left,
            rw list.mem_append,
            right,
            apply list.mem_cons_self,
          },
          have glruf : good_letter (symbol.nonterminal r.fst),
          {
            exact ih.right (symbol.nonterminal r.fst) ruu,
          },
          unfold good_letter at glruf,
          rw h at glruf,
          cases glruf with n₀ imposs,
          exact option.no_confusion imposs,
        },
        cases (option.ne_none_iff_exists'.mp h) with x ex,
        use x,
        have gix := lifted_grammar_inverse lg r.fst ⟨x, ex⟩,
        rw ex at gix,
        rw option.map_some' at gix,
        apply option.some_injective,
        exact gix,
      },
      rcases lg.preimage_of_rules r ⟨in_rules, exn₀⟩ with ⟨r₀, in0, lif⟩,
      rw ←lif at in_y,
      unfold lift_rule at in_y,
      dsimp only at in_y,
      unfold lift_string at in_y,
      rw list.mem_map at in_y,
      rcases in_y with ⟨s, s_in_rulsnd, symbol_letter⟩,
      rw ←symbol_letter,
      cases s,
      {
        unfold lift_symbol,
      },
      unfold lift_symbol,
      unfold good_letter,
      use s,
      exact lg.lift_nt_sink s,
    },
    {
      apply ihr,
      right,
      exact in_y,
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
