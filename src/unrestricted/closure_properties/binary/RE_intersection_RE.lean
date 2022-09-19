import unrestricted.closure_properties.binary.RE_concatenation_RE


def super_nonterminal (T N₁ N₂ : Type) : Type :=
(option (N₁ ⊕ T)) × ((N₂ ⊕ T) ⊕ (((N₂ ⊕ T) × (N₂ ⊕ T)) ⊕ (fin 2)))


variable {T : Type}

def rule_step_right {N₁ N₂ : Type} (s₁ s₂ : option (N₁ ⊕ T)) (x y z : N₂ ⊕ T) :
  frule T (super_nonterminal T N₁ N₂) :=
frule.mk
  [symbol.nonterminal (s₁, sum.inr (sum.inl (x, y))), symbol.nonterminal (s₂, sum.inl z)]
  (s₁, sum.inr (sum.inl (x, y)))
  (list.mem_cons_self _ _)
  [symbol.nonterminal (s₁, sum.inl x), symbol.nonterminal (s₂, sum.inr (sum.inl (y, z)))]

def rule_step_right_end {N₁ N₂ : Type} (s₁ s₂ : option (N₁ ⊕ T)) (x y : N₂ ⊕ T) :
  frule T (super_nonterminal T N₁ N₂) :=
frule.mk
  [symbol.nonterminal (s₁, sum.inr (sum.inl (x, y))), symbol.nonterminal (s₂, sum.inr (sum.inr 0))]
  (s₁, sum.inr (sum.inl (x, y)))
  (list.mem_cons_self _ _)
  [symbol.nonterminal (s₁, sum.inl x), symbol.nonterminal (s₂, sum.inl y)]

def rule_step_left {N₁ N₂ : Type} (s₁ s₂ : option (N₁ ⊕ T)) (x : N₂ ⊕ T) :
  frule T (super_nonterminal T N₁ N₂) :=
frule.mk
  [symbol.nonterminal (s₁, sum.inr (sum.inr 1)), symbol.nonterminal (s₂, sum.inl x)]
  (s₁, sum.inr (sum.inr 1))
  (list.mem_cons_self _ _)
  [symbol.nonterminal (s₁, sum.inl x), symbol.nonterminal (s₂, sum.inr (sum.inr 1))]

def rule_step_left_end {N₁ N₂ : Type} (s₁ s₂ : option (N₁ ⊕ T)) :
  frule T (super_nonterminal T N₁ N₂) :=
frule.mk
  [symbol.nonterminal (s₁, sum.inr (sum.inr 1)), symbol.nonterminal (s₂, sum.inr (sum.inr 0))]
  (s₁, sum.inr (sum.inr 1))
  (list.mem_cons_self _ _)
  [symbol.nonterminal (s₁, sum.inr (sum.inr 0)), symbol.nonterminal (s₂, sum.inr (sum.inr 0))]

def rule_finalize_terminal {N₁ N₂ : Type} (t : T) :
  frule T (super_nonterminal T N₁ N₂) :=
frule.mk
  [symbol.nonterminal (some (sum.inr t), sum.inl (sum.inr t))]
  (some (sum.inr t), sum.inl (sum.inr t))
  (list.mem_singleton_self _)
  [symbol.terminal t]

def rule_delete_empty_empty {N₁ N₂ : Type} :
  frule T (super_nonterminal T N₁ N₂) :=
frule.mk
  [symbol.nonterminal (none, sum.inr (sum.inr 0))]
  (none, sum.inr (sum.inr 0))
  (list.mem_singleton_self _)
  []


def all_used_terminals_f (g : frammar T) : list T :=
list.filter_map as_terminal (list.join (list.map frule.output_string g.rules))

def rules_finalize_terminal (g₁ g₂ : frammar T) :
  list (frule T (super_nonterminal T g₁.nt g₂.nt)) :=
list.map (λ t, rule_finalize_terminal t) (all_used_terminals_f g₁ ++ all_used_terminals_f g₂)
-- intersection of `all_used_terminals_f g₁` and `all_used_terminals_f g₂` should be sufficient
-- maybe just use one of them (whichever is more convenient for the proof at the end)

def all_used_nonterminals_f (g : frammar T) : list g.nt :=
sorry

def rules_step_left_end (g₁ g₂ : frammar T) :
  list (frule T (super_nonterminal T g₁.nt g₂.nt)) :=
let z := option.none ::
  (list.map (option.some ∘ sum.inl) (all_used_nonterminals_f g₁)) ++
  (list.map (option.some ∘ sum.inr) (all_used_terminals_f g₁))
in list.join (z.map (λ s₁, z.map (λ s₂, rule_step_left_end s₁ s₂)))


/-- The class of recursively-enumerable languages is closed under intersection. -/
theorem RE_of_RE_i_RE (L₁ : language T) (L₂ : language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ ⊓ L₂)   :=
begin
  repeat {
    rw is_fRE_of_is_RE,
  },
  rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩,
  sorry,
end
