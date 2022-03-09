import cfg
import tactic


variables {T : Type}


def lift_symbol {N₁ N : Type} (lift_N : N₁ → N) : symbol T N₁ → symbol T N
| (symbol.terminal ter) := symbol.terminal ter
| (symbol.nonterminal nonter) := symbol.nonterminal (lift_N nonter)

def lift_grammar (g₁ : CF_grammar T) {N : Type} (lift_N : g₁.nt → N)
                 (lift_N_inj : function.injective lift_N) : CF_grammar T :=
CF_grammar.mk N (lift_N g₁.initial) (list.map (λ r : g₁.nt × (list (symbol T g₁.nt)), 
    (lift_N r.fst, list.map (lift_symbol lift_N) r.snd)) g₁.rules)

lemma lift_tran (g₁ : CF_grammar T) {N : Type} (lift_N : g₁.nt → N)
                (lift_N_inj : function.injective lift_N)
                (input output : list (symbol T g₁.nt))
                (hyp : CF_transforms g₁ input output) :
  CF_transforms (lift_grammar g₁ lift_N lift_N_inj)
                (list.map (lift_symbol lift_N) input)
                (list.map (lift_symbol lift_N) output) :=
begin
  rcases hyp with ⟨ rule, rule_in, v, w, ass ⟩,
  use (lift_N rule.fst, list.map (lift_symbol lift_N) rule.snd),
  split,
  {

    sorry,
  },
  simp,
  /-have achjo : (lift_grammar g₁ lift_N lift_N_inj).nt = N, refl,
  rw achjo,
  use map (lift_symbol lift_N) v,-/
  sorry,
end

lemma lift_deri (g₁ : CF_grammar T) {N : Type} (lift_N : g₁.nt → N)
                (lift_N_inj : function.injective lift_N)
                (input output : list (symbol T g₁.nt))
                (hyp : CF_derives g₁ input output) :
  CF_derives (lift_grammar g₁ lift_N lift_N_inj)
             (list.map (lift_symbol lift_N) input)
             (list.map (lift_symbol lift_N) output) :=
begin

  sorry,
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
  let sinked_grammar := lift_grammar (lift_grammar g₁ lift_N lift_N_inj) sink_N sorry,

  sorry,
end

lemma sink_deri (g₁ : CF_grammar T) {N : Type} 
                (lift_N : g₁.nt → N) (sink_N : N → g₁.nt)
                (lift_N_inj : function.injective lift_N)
                (lift_N_sink : ∀ n₁ : g₁.nt, sink_N (lift_N n₁) = n₁)
                (input output : list (symbol T N))
                (hyp : CF_derives (lift_grammar g₁ lift_N lift_N_inj) input output) :
  CF_derives g₁ (list.map (lift_symbol sink_N) input) (list.map (lift_symbol sink_N) output) :=
begin

  sorry,
end





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



private lemma deri₁_step (g₁ g₂ : CF_grammar T)
                         (input output : list (symbol T g₁.nt))
                         (hyp : CF_transforms g₁ input output) :
  CF_transforms (combined_grammar g₁ g₂) (lsTN_of_lsTN₁ input) (lsTN_of_lsTN₁ output) :=
begin
  --exact lift_tran (lift_grammar g₁ (λ n₁, option.some (sum.inl n₁)) sorry) input output sorry,
  sorry,
end


/-- The class of context-free languages is closed under concatenation. -/
theorem CF_of_CF_c_CF {T : Type} (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ * L₂)   :=
sorry
