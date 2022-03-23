import context_free.cfg
import tactic

-- This file is now extremely messy. Read at your own risk.


section reusable_defs_and_lemmata

lemma list_map_append_append {α β : Type} {x y z : list α} {f : α → β} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by simp only [list.map_append]


variable {T : Type}

def lift_symbol {N₁ N : Type} (lift_N : N₁ → N) : symbol T N₁ → symbol T N
| (symbol.terminal ter) := symbol.terminal ter
| (symbol.nonterminal nonter) := symbol.nonterminal (lift_N nonter)

def lift_string {N₁ N : Type} (lift_N : N₁ → N) :
  list (symbol T N₁) → list (symbol T N) :=
list.map (lift_symbol lift_N)

def lift_rule {N₁ N : Type} (lift_N : N₁ → N) :
  N₁ × (list (symbol T N₁)) → N × (list (symbol T N)) :=
λ r, (lift_N r.fst, lift_string lift_N r.snd)

-- we should somehow allow to have only a subset of rules here
-- but how to define it ??
def lift_grammar (g₁ : CF_grammar T) {N : Type} (lift_N : g₁.nt → N)
                 (lift_N_inj : function.injective lift_N) :
  CF_grammar T :=
CF_grammar.mk N (lift_N g₁.initial) (list.map (lift_rule lift_N) g₁.rules)


lemma lift_tran (g₁ : CF_grammar T) {N : Type} (lift_N : g₁.nt → N)
                (lift_N_inj : function.injective lift_N)
                (input output : list (symbol T g₁.nt))
                (hyp : CF_transforms g₁ input output) :
  CF_transforms (lift_grammar g₁ lift_N lift_N_inj)
                (lift_string lift_N input)
                (lift_string lift_N output) :=
begin
  rcases hyp with ⟨ rule, rule_in, v, w, ass ⟩,
  use lift_rule lift_N rule,
  split,
  {
    delta lift_grammar,
    simp only [lift_grammar, list.mem_map, prod.mk.inj_iff],
    use rule,
    split,
    {
      exact rule_in,
    },
    split;
    refl,
  },
  simp,
  use lift_string lift_N v,
  use lift_string lift_N w,
  cases ass with bef aft,
  split;
  {
    unfold lift_string,
    finish,
  },
end

lemma lift_deri (g₁ : CF_grammar T) {N : Type} (lift_N : g₁.nt → N)
                (lift_N_inj : function.injective lift_N)
                (input output : list (symbol T g₁.nt))
                (hyp : CF_derives g₁ input output) :
  CF_derives (lift_grammar g₁ lift_N lift_N_inj)
             (lift_string lift_N input)
             (lift_string lift_N output) :=
begin
  induction hyp with u v trash orig ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  exact lift_tran g₁ lift_N lift_N_inj u v orig,
end

lemma lift_generates (g₁ : CF_grammar T) {N : Type} (lift_N : g₁.nt → N)
                     (lift_N_inj : function.injective lift_N)
                     (w : list T) (hyp : CF_generates g₁ w) :
  CF_generates (lift_grammar g₁ lift_N lift_N_inj) w :=
begin
  change CF_derives g₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal w) at hyp,
  let g := (lift_grammar g₁ lift_N lift_N_inj),
  change CF_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w),
  have h₁ := lift_deri g₁ lift_N lift_N_inj [symbol.nonterminal g₁.initial] (list.map symbol.terminal w) hyp,
  unfold lift_string at h₁,
  rw list.map_singleton at h₁,
  rw lift_symbol at h₁,
  simp at h₁,
  exact h₁,
end


lemma sink_tran (g₁ : CF_grammar T) {N : Type} 
                (lift_N : g₁.nt → N) (sink_N : N → g₁.nt)
                (lift_N_inj : function.injective lift_N)
                (lift_N_sink : ∀ n₁ : g₁.nt, sink_N (lift_N n₁) = n₁)
                (input output : list (symbol T N))
                (hyp : CF_transforms (lift_grammar g₁ lift_N lift_N_inj) input output) :
  CF_transforms g₁ (list.map (lift_symbol sink_N) input) (list.map (lift_symbol sink_N) output) :=
begin
  rcases hyp with ⟨ rule, rule_in, v, w, bef, aft ⟩,
  unfold CF_transforms,
  let sinked_rule := lift_rule sink_N rule,
  change rule ∈ (list.map (lift_rule lift_N) g₁.rules) at rule_in,
  use sinked_rule,
  split,
  {
    change lift_rule sink_N rule ∈ g₁.rules,
    rw list.mem_map at rule_in,
    rcases rule_in with ⟨ the_rule, the_in, the_hyp ⟩,
    rw ← the_hyp,
    convert the_in,
    ext1,
    {
      unfold lift_rule,
      dsimp,
      rw lift_N_sink,
    },
    {
      unfold lift_rule,
      unfold lift_string,
      dsimp,
      rw list.map_map,
      have lift_sink_eq_id : lift_symbol sink_N ∘ lift_symbol lift_N = id,
      {
        ext1,
        cases x,
        {
          refl,
        },
        delta lift_symbol,
        dsimp,
        rw lift_N_sink,
      },
      rw lift_sink_eq_id,
      exact the_rule.snd.map_id,
    },
  },
  use lift_string sink_N v,
  use lift_string sink_N w,
  split,
  {
    rw bef,
    rw lift_string,
    rw list_map_append_append,
    rw list.map_singleton,
    refl,
  },
  {
    rw aft,
    rw lift_string,
    rw list_map_append_append,
    refl,
  },
end

lemma sink_deri (g₁ : CF_grammar T) {N : Type} 
                (lift_N : g₁.nt → N) (sink_N : N → g₁.nt)
                (lift_N_inj : function.injective lift_N)
                (lift_N_sink : ∀ n₁ : g₁.nt, sink_N (lift_N n₁) = n₁)
                (input output : list (symbol T N))
                (hyp : CF_derives (lift_grammar g₁ lift_N lift_N_inj) input output) :
  CF_derives g₁ (list.map (lift_symbol sink_N) input) (list.map (lift_symbol sink_N) output) :=
begin
  induction hyp with u v trash orig ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  exact sink_tran g₁ lift_N sink_N lift_N_inj lift_N_sink u v orig,
end

lemma sink_generates (g₁ : CF_grammar T) {N : Type}
                     (lift_N : g₁.nt → N) (sink_N : N → g₁.nt)
                     (lift_N_inj : function.injective lift_N)
                     (lift_N_sink : ∀ n₁ : g₁.nt, sink_N (lift_N n₁) = n₁)
                     (w : list T)
                     (hyp : CF_generates (lift_grammar g₁ lift_N lift_N_inj) w) :
  CF_generates g₁ w :=
begin
  let g := (lift_grammar g₁ lift_N lift_N_inj),
  change CF_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w) at hyp,
  change CF_derives g₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal w),
  have h₁ := sink_deri g₁ lift_N sink_N lift_N_inj lift_N_sink
                       [symbol.nonterminal g.initial]
                       (list.map symbol.terminal w)
                       hyp,
  rw list.map_singleton at h₁,
  rw lift_symbol at h₁,
  simp at h₁,
  convert h₁,
  change g₁.initial = sink_N (lift_N g₁.initial),
  rw lift_N_sink,
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
  (((list.map rule_of_rule₁ gₗ.rules) ++ (list.map rule_of_rule₂ gᵣ.rules)))


/-- The class of context-free languages is closed under concatenation. -/
theorem CF_of_CF_c_CF (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ * L₂)   :=
sorry
