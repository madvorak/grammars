import cfg
import computability.DFA


def is_Reg {T : Type} (L : language T) :=
∃ σ : Type, ∃ a : DFA T σ, a.accepts = L

def is_CF {T : Type} (L : language T) :=
∃ g : CF_grammar T, CF_language g = L


theorem CF_under_union {T : Type} (L₁ : language T) (L₂ : language T) :
is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ + L₂) :=
begin
  intro input,
  cases input with cf₁ cf₂,

  cases cf₁ with g₁ h₁,
  cases cf₂ with g₂ h₂,

  let N₁ : Type := g₁.nt,
  let N₂ : Type := g₂.nt,
  let N : Type := option (N₁ ⊕ N₂),
  
  let rules₁ : list (N × (list (symbol T N))) :=
    list.map 
      (λ x, (
        (some (sum.inl (prod.fst x))),
        (list.map (λ elem : (symbol T N₁), match elem with
          | symbol.terminal st := (symbol.terminal st)
          | symbol.nonterminal snt := (symbol.nonterminal (some (sum.inl snt)))
        end) (prod.snd x))
      ))
      g₁.rules,
  
  let rules₂ : list (N × (list (symbol T N))) :=
    list.map 
      (λ x, (
        (some (sum.inr (prod.fst x))),
        (list.map (λ elem : (symbol T N₂), match elem with
          | symbol.terminal st := (symbol.terminal st)
          | symbol.nonterminal snt := (symbol.nonterminal (some (sum.inr snt)))
        end) (prod.snd x))
      ))
      g₂.rules,

  let g := CF_grammar.mk N none (
    (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
    (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
    rules₁ ++ rules₂),
  use g,
  
  apply set.eq_of_subset_of_subset,
  {
    -- prove `CF_language g ⊆ L₁ + L₂`
    intros w h,
    simp,
    unfold CF_language at h,
    change CF_generates_str g (list.map symbol.terminal w) at h,
    sorry,
  },
  
  -- prove `L₁ + L₂ ⊆ CF_language g`
  intros w h,
  rw language.mem_add at h,
  
  cases h with case₁ case₂,
  {
    have deri_orig : CF_derives g₁ [symbol.nonterminal g₁.initial] (list.map symbol.terminal w),
    {
      finish,
    },

    have deri_rest : CF_derives g [symbol.nonterminal (some (sum.inl g₁.initial))] (list.map symbol.terminal w),
    {
      dsimp at *,
      sorry,
    },

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

    unfold CF_language,
    change CF_generates_str g (list.map symbol.terminal w),
    unfold CF_generates_str,
    unfold CF_derives,
    apply @trans _ (CF_derives g) (is_trans.mk relation.transitive_refl_trans_gen),
      finish, -- uses `deri_start` here
    exact deri_rest,
  },

  sorry, -- prove case₂ symmetrically
end


theorem CF_intersection_Reg {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
is_CF L₁ ∧ is_Reg L₂ → is_CF (set.inter L₁ L₂) :=
sorry


theorem CF_under_concatenation {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ * L₂) :=
sorry
