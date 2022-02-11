import cfg

/-
def is_CF {T : Type} [fintype T] {N : Type} [fintype N] (L : language T) :=
∃ g : CF_grammar T N, CF_language g = L
-/
def is_CF {T : Type} [T_fin : fintype T] (L : language T) :=
∃ N : Type, ∃ N_fin : fintype N, ∃ g : @CF_grammar T N T_fin N_fin, @CF_language T N T_fin N_fin g = L


theorem CF_of_CF_union_CF {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
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
  have N_fin : fintype N, sorry,
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
  
  use @CF_grammar.mk T N T_fin N_fin root ([
    (root, [@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inl (@CF_grammar.initial T N₁ T_fin N₁fin g₁)))]),
    (root, [@symbol.nonterminal T N T_fin N_fin (sum.inl (sum.inr (@CF_grammar.initial T N₂ T_fin N₂fin g₂)))])
  ] ++ rules₁ ++ rules₂),
  
  sorry,
end