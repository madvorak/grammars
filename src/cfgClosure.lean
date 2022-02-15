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
  /-
  -- prove `L₁ + L₂ ⊆ CF_language g`
  intros w h,
  rw language.mem_add at h,
  cases h with case₁ case₂,
  {
    have deri_orig : @CF_derives T N₁ T_fin N₁fin g₁
                     [@symbol.nonterminal T N₁ T_fin N₁fin (@CF_grammar.initial T N₁ T_fin N₁fin g₁)]
                     (list.map (@symbol.terminal T N₁ T_fin N₁fin) w),
    {
      finish,
    },

    have deri_rest : @CF_derives T N T_fin N_fin g
                     [@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inl (@CF_grammar.initial T N₁ T_fin N₁fin g₁)))]
                     (list.map (@symbol.terminal T N T_fin N_fin) w),
    {
      dsimp at *,
      induction deri_orig,
        sorry, -- base step
      fconstructor,
        exact list.map (λ s : @symbol T N₁ T_fin N₁fin, match s with
          | @symbol.terminal T N₁ T_fin N₁fin st := (@symbol.terminal T N T_fin N_fin st)
          | @symbol.nonterminal T N₁ T_fin N₁fin snt := (@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inl snt)))
        end) deri_orig_b,
      {
        simp,
        sorry, -- almost exact `deri_orig_ᾰ`
      },
      -- how is `deri_orig_c` related to `w` ???
      sorry,
    },

    have deri_start : @CF_derives T N T_fin N_fin g
                      [@symbol.nonterminal T N T_fin N_fin root]
                      [@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inl (@CF_grammar.initial T N₁ T_fin N₁fin g₁)))],
    {
      fconstructor,
        exact [@symbol.nonterminal T N T_fin N_fin root],
      refl,
      use (root, [@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inl (@CF_grammar.initial T N₁ T_fin N₁fin g₁)))]),
      split,
        finish,
      use [[], []],
      simp,
    },

    unfold CF_language,
    change @CF_generates_str T N T_fin N_fin g 
      (list.map (@symbol.terminal T N T_fin N_fin) w),
    unfold CF_generates_str,
    change @CF_derives T N T_fin N_fin g 
      [@symbol.nonterminal T N T_fin N_fin root]
      (list.map (@symbol.terminal T N T_fin N_fin) w),
    unfold CF_derives,
    have tranz : is_trans _ (relation.refl_trans_gen (@CF_transforms T N T_fin N_fin g)) := 
      is_trans.mk relation.transitive_refl_trans_gen,
    apply @trans _ (@CF_derives T N T_fin N_fin g) tranz,
      finish, -- uses deri_start
    exact deri_rest,
  },

  sorry, -- prove case₂ symmetrically
  -/
  sorry
end


theorem CF_intersection_Reg {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
is_CF L₁ ∧ is_Reg L₂ → is_CF (set.inter L₁ L₂) :=
sorry


theorem CF_under_concatenation {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ * L₂) :=
sorry
