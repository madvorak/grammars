import context_free.cfg
import tactic


section reusable_defs_and_lemmata

lemma list_map_append_append {α β : Type} {x y z : list α} {f : α → β} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by simp only [list.map_append]


variable {T : Type}

def lift_symbol {N₁ N : Type} (lift_N : N₁ → N) : symbol T N₁ → symbol T N
| (symbol.terminal ter) := symbol.terminal ter
| (symbol.nonterminal nonter) := symbol.nonterminal (lift_N nonter)

def sink_symbol {N N₁ : Type} (sink_N : N → option N₁) : symbol T N → option (symbol T N₁)
| (symbol.terminal ter) := some (symbol.terminal ter)
| (symbol.nonterminal nonter) := option.map symbol.nonterminal (sink_N nonter)

def lift_string {N₁ N : Type} (lift_N : N₁ → N) :
  list (symbol T N₁) → list (symbol T N) :=
list.map (lift_symbol lift_N)

def sink_string {N N₁ : Type} (sink_N : N → option N₁) :
  list (symbol T N) → list (symbol T N₁) :=
list.filter_map (sink_symbol sink_N)

def lift_rule {N₁ N : Type} (lift_N : N₁ → N) :
  N₁ × (list (symbol T N₁)) → N × (list (symbol T N)) :=
λ r, (lift_N r.fst, lift_string lift_N r.snd)

structure lifted_grammar :=
(g₁ g₂ : CF_grammar T)
(lift_nt : g₁.nt → g₂.nt)
(lift_inj : function.injective lift_nt)
(corresponding_rules : ∀ r : g₁.nt × list (symbol T g₁.nt),
  r ∈ g₁.rules →
    lift_rule lift_nt r ∈ g₂.rules
)
(preimage_of_rules : ∀ r₂ : g₂.nt × list (symbol T g₂.nt),
  (∃ n₁ : g₁.nt, lift_nt n₁ = r₂.fst) →
    (∃ r₁ ∈ g₁.rules, lift_rule lift_nt r₁ = r₂)
)
(sink_nt : g₂.nt → option g₁.nt)
(lift_nt_sink : ∀ n₁ : g₁.nt, sink_nt (lift_nt n₁) = some n₁)


lemma lift_tran (lg : lifted_grammar)
                (input output : list (symbol T lg.g₁.nt))
                (hyp : CF_transforms lg.g₁ input output) :
  CF_transforms lg.g₂ (lift_string lg.lift_nt input) (lift_string lg.lift_nt output) :=
begin
  rcases hyp with ⟨ rule, rule_in, v, w, ass ⟩,
  sorry,
end

lemma lift_deri (lg : lifted_grammar)
                (input output : list (symbol T lg.g₁.nt))
                (hyp : CF_derives lg.g₁ input output) :
  CF_derives lg.g₂ (lift_string lg.lift_nt input) (lift_string lg.lift_nt output) :=
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


lemma sink_tran (lg : lifted_grammar)
                (input output : list (symbol T lg.g₂.nt))
                (hyp : CF_transforms lg.g₂ input output) :
  CF_transforms lg.g₁ (sink_string lg.sink_nt input) (sink_string lg.sink_nt output) :=
begin
  rcases hyp with ⟨ rule, rule_in, v, w, bef, aft ⟩,
  sorry,
end

lemma sink_deri (lg : lifted_grammar)
                (input output : list (symbol T lg.g₂.nt))
                (hyp : CF_derives lg.g₂ input output) :
  CF_derives lg.g₁ (sink_string lg.sink_nt input) (sink_string lg.sink_nt output) :=
begin
  induction hyp with u v trash orig ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  exact sink_tran lg u v orig,
end


end reusable_defs_and_lemmata


variable {T : Type}

private def sTN_of_sTN₁ {g₁ g₂ : CF_grammar T} : (symbol T g₁.nt) → (symbol T (option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inl snt)))

private def sTN_of_sTN₂ {g₁ g₂ : CF_grammar T} : (symbol T g₂.nt) → (symbol T (option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inr snt)))

private def lsTN_of_lsTN₁ {g₁ g₂ : CF_grammar T} :
  list (symbol T g₁.nt) → list (symbol T (option (g₁.nt ⊕ g₂.nt))) :=
list.map sTN_of_sTN₁

private def lsTN_of_lsTN₂ {g₁ g₂ : CF_grammar T} :
  list (symbol T g₂.nt) → list (symbol T (option (g₁.nt ⊕ g₂.nt))) :=
list.map sTN_of_sTN₂

private def rule_of_rule₁ {g₁ g₂ : CF_grammar T} (r : g₁.nt × (list (symbol T g₁.nt))) :
  ((option (g₁.nt ⊕ g₂.nt)) × (list (symbol T (option (g₁.nt ⊕ g₂.nt))))) :=
(some (sum.inl (prod.fst r)), lsTN_of_lsTN₁ (prod.snd r))

private def rule_of_rule₂ {g₁ g₂ : CF_grammar T} (r : g₂.nt × (list (symbol T g₂.nt))) :
  ((option (g₁.nt ⊕ g₂.nt)) × (list (symbol T (option (g₁.nt ⊕ g₂.nt))))) :=
(some (sum.inr (prod.fst r)), lsTN_of_lsTN₂ (prod.snd r))

private def combined_grammar (gₗ gᵣ : CF_grammar T) :
  CF_grammar T :=
CF_grammar.mk (option (gₗ.nt ⊕ gᵣ.nt)) none
  ((none, [symbol.nonterminal (some (sum.inl (gₗ.initial))), symbol.nonterminal (some (sum.inr (gᵣ.initial)))]) ::
    ((list.map rule_of_rule₁ gₗ.rules) ++ (list.map rule_of_rule₂ gᵣ.rules)))



lemma in_language_asdf {g₁ g₂ : CF_grammar T} (w : list T)
                       (hyp : w ∈ CF_language (combined_grammar g₁ g₂)) :
  w ∈ CF_language g₁ * CF_language g₂ :=
begin
  -- we need to do sinking here
  rw language.mem_mul,
  sorry,
end

private def oN₁_of_N {g₁ g₂ : CF_grammar T} : (combined_grammar g₁ g₂).nt → (option g₁.nt)
| none := none
| (some (sum.inl nonte)) := some nonte
| (some (sum.inr _)) := none

lemma in_language_qwert {g₁ g₂ : CF_grammar T} (w : list T)
                        (hyp : w ∈ CF_language g₁ * CF_language g₂) :
  w ∈ CF_language (combined_grammar g₁ g₂) :=
begin
  -- we need to do lifting here
  rw language.mem_mul at hyp,
  rcases hyp with ⟨ u, v, hu, hv, hw ⟩,
  unfold CF_language at *,
  change CF_derives (combined_grammar g₁ g₂)
                    [symbol.nonterminal (combined_grammar g₁ g₂).initial]
                    (list.map symbol.terminal w),

  -- TODO this lifted_grammar `gg` works only for the left part
  let gg := lifted_grammar.mk g₁ (combined_grammar g₁ g₂) (some ∘ sum.inl) (by {
    -- prove `function.injective (some ∘ sum.inl)` here
    intros x y h,
    apply sum.inl_injective,
    apply option.some_injective,
    exact h,
  }) (by {
    -- prove `∀ r ∈ g₁.rules` we have `lift_rule (some ∘ sum.inl) r ∈ list.map rule_of_rule₁ g₁.rules` here
    intros r h,
    apply list.mem_cons_of_mem,
    apply list.mem_append_left,
    rw list.mem_map,
    use r,
    split,
    {
      exact h,
    },
    unfold rule_of_rule₁,
    unfold lift_rule,
    norm_num,
    unfold lift_string,
    unfold lsTN_of_lsTN₁,
    apply congr_fun,
    apply congr_arg,
    ext1,
    cases x;
    refl,
  }) (by /- preimage_of_rules -/ sorry) oN₁_of_N (by { intro, refl }),

  apply @CF_deri_of_tran_deri T (combined_grammar g₁ g₂) _ [symbol.nonterminal (some (sum.inl (g₁.initial))), symbol.nonterminal (some (sum.inr (g₂.initial)))] _,
  {

    sorry,
  },
  rw ← hw,
  rw list.map_append,
  apply @CF_deri_of_deri_deri T (combined_grammar g₁ g₂) _ (list.map symbol.terminal u ++ [symbol.nonterminal (some (sum.inr g₂.initial))]) _,
  {
    change CF_derives (combined_grammar g₁ g₂) ([symbol.nonterminal (some (sum.inl g₁.initial))] ++ [symbol.nonterminal (some (sum.inr g₂.initial))]) (list.map symbol.terminal u ++ [symbol.nonterminal (some (sum.inr g₂.initial))]),
    apply CF_derives_with_postfix,

    change CF_derives g₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal u) at hu,
    change CF_derives gg.g₂ [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal u),
    
    have bar : [symbol.nonterminal (some (sum.inl g₁.initial))] = list.map (lift_symbol gg.lift_nt) [symbol.nonterminal g₁.initial],
    {
      apply list.singleton_eq,
    },
    rw bar,

    have baz : list.map symbol.terminal u = list.map (lift_symbol gg.lift_nt) (list.map symbol.terminal u),
    {
      rw list.map_map,
      apply congr_fun,
      apply congr_arg,
      refl,
    },
    rw baz,
    
    exact lift_deri gg [symbol.nonterminal g₁.initial] (list.map symbol.terminal u) hu,
  },
  {
    apply CF_derives_with_prefix,

    change CF_derives g₂ [symbol.nonterminal g₂.initial] (list.map symbol.terminal v) at hv,

    sorry,
  },
end

/-- The class of context-free languages is closed under concatenation. -/
theorem CF_of_CF_c_CF (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ * L₂)   :=
begin
  rintro ⟨ ⟨ g₁, h₁ ⟩, ⟨ g₂, h₂ ⟩ ⟩,

  use combined_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    -- prove `L₁ * L₂ ⊇ ` here
    intros w hyp,
    rw ← h₁,
    rw ← h₂,
    exact in_language_asdf w hyp,
  },
  {
    -- prove `L₁ * L₂ ⊆ ` here
    intros w hyp,
    rw ← h₁ at hyp,
    rw ← h₂ at hyp,
    exact in_language_qwert w hyp,
  },
end
