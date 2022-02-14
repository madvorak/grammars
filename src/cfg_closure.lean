import cfg


def is_CF {T : Type} [T_fin : fintype T] (L : language T) :=
∃ N : Type, ∃ N_fin : fintype N, ∃ g : @CF_grammar T N T_fin N_fin, @CF_language T N T_fin N_fin g = L


theorem CF_under_union {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ + L₂) :=
begin
  intro input,
  cases input with cf₁ cf₂,

  cases cf₁ with N₁ foo₁,
  cases foo₁ with N₁fin bar₁,
  cases bar₁ with g₁ h₁,
  
  cases cf₂ with N₂ foo₂,
  cases foo₂ with N₂fin bar₂,
  cases bar₂ with g₂ h₂,

  let N : Type := (N₁ ⊕ N₂) ⊕ (fin 1),
  use N,
  have N_fin : fintype N,
  {
    have N₁N₂fin : fintype (N₁ ⊕ N₂) :=
      @sum.fintype N₁ N₂ N₁fin N₂fin,
    exact @sum.fintype (N₁ ⊕ N₂) (fin 1) N₁N₂fin _,
  },
  use N_fin,
  let root : N := (sum.inr (0 : fin 1)),
  
  let rules₁ : list (N × (list (@symbol T N T_fin N_fin))) :=
    list.map (λ x,
      ((sum.inl (sum.inl (prod.fst x)),
      list.map (λ elem : (@symbol T N₁ T_fin N₁fin), match elem with
        | @symbol.terminal T N₁ T_fin N₁fin st := (@symbol.terminal T N T_fin N_fin st)
        | @symbol.nonterminal T N₁ T_fin N₁fin snt := (@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inl snt)))
      end)
      (prod.snd x)
    )))
    (@CF_grammar.rules T N₁ T_fin N₁fin g₁),

  let rules₂ : list (N × (list (@symbol T N T_fin N_fin))) :=
    list.map (λ x,
      ((sum.inl (sum.inr (prod.fst x)),
      list.map (λ elem : (@symbol T N₂ T_fin N₂fin), match elem with
        | @symbol.terminal T N₂ T_fin N₂fin st := (@symbol.terminal T N T_fin N_fin st)
        | @symbol.nonterminal T N₂ T_fin N₂fin snt := (@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inr snt)))
      end)
      (prod.snd x)
    )))
    (@CF_grammar.rules T N₂ T_fin N₂fin g₂),
  
  let g := @CF_grammar.mk T N T_fin N_fin root ([
    (root, [@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inl (@CF_grammar.initial T N₁ T_fin N₁fin g₁)))]),
    (root, [@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inr (@CF_grammar.initial T N₂ T_fin N₂fin g₂)))])
  ] ++ rules₁ ++ rules₂),
  use g,
  
  apply set.eq_of_subset_of_subset,
  {
    -- prove `CF_language g ⊆ L₁ + L₂`
    intros w h,
    simp,
    unfold CF_language at h,
    change @CF_generates_str T N T_fin N_fin g (list.map (@symbol.terminal T N T_fin N_fin) w) at h,
    sorry,
  },

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
end
