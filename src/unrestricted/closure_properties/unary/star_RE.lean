import unrestricted.closure_properties.binary.RE_concatenation_RE


-- new nonterminal type
private def nn (N : Type) : Type :=
N ⊕ fin 3

-- new symbol type
private def ns (T N : Type) : Type :=
symbol T (nn N)


variables {T : Type}

private def Z {N : Type} : ns T N := symbol.nonterminal (sum.inr 0)
private def H {N : Type} : ns T N := symbol.nonterminal (sum.inr 1) -- originally denoted `#`
private def R {N : Type} : ns T N := symbol.nonterminal (sum.inr 2)

private def S {g : grammar T} : ns T g.nt := symbol.nonterminal (sum.inl g.initial)


private def wrap_sym {N : Type} : symbol T N → ns T N
| (symbol.terminal t)    := symbol.terminal t
| (symbol.nonterminal n) := symbol.nonterminal (sum.inl n)

private def wrap_gr {N : Type} (r : grule T N) : grule T (nn N) :=
grule.mk
  (list.map wrap_sym r.input_L)
  (sum.inl r.input_N)
  (list.map wrap_sym r.input_R)
  (list.map wrap_sym r.output_string)

private def rules_that_scan_terminals (g : grammar T) : list (grule T (nn g.nt)) :=
list.map (λ t,  -- `Rt → tR`
    grule.mk [] (sum.inr 2) [symbol.terminal t] [symbol.terminal t, R]
  ) (all_used_terminals g)

-- based on `/informal/KleeneStar.pdf`
private def star_grammar (g : grammar T) : grammar T :=
grammar.mk (nn g.nt) (sum.inr 0) (
  (grule.mk [] (sum.inr 0) [] [Z, S, H]) ::
  (grule.mk [] (sum.inr 0) [] [R, H]) ::
  (grule.mk [] (sum.inr 2) [H] [R]) ::
  (grule.mk [] (sum.inr 0) [] []) ::
  list.map wrap_gr g.rules ++
  rules_that_scan_terminals g
)


private lemma star_induction {g : grammar T} {α : list (ns T g.nt)}
    (ass : grammar_derives (star_grammar g) [Z] α) :
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = [Z] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ x : list (list (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = [R, H] ++ list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ w : list (list T), ∃ β : list T, ∃ γ : list (symbol T g.nt), ∃ x : list (list (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = (list.map symbol.terminal (list.join w)) ++ [R, H] ++
      list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)))) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ α = list.map symbol.terminal u) ∨
  (∃ σ : list (symbol T g.nt), α = list.map wrap_sym σ ++ [R]) ∨
  (∃ ω : list (symbol T g.nt), α = list.map wrap_sym ω ++ [H] ∧ Z ∉ α ∧ R ∉ α) :=
begin
  induction ass with a b trash orig ih,
  {
    left,
    use list.nil,
    tauto,
  },
  cases ih,
  {
    rcases ih with ⟨x, valid, cat⟩,
    rw cat at *,
    clear cat,
    rcases orig with ⟨r, rin, u, v, bef, aft⟩,
    cases rin,
    {
      left,
      rw rin at *,
      clear rin,
      dsimp at *,
      use ([symbol.nonterminal g.initial] :: x),
      split,
      {
        intros xᵢ xin,
        cases xin,
        {
          rw xin,
          apply grammar_deri_self,
        },
        {
          exact valid xᵢ xin,
        },
      },
      have u_nil : u = [],
      {
        -- follows from `bef`
        sorry,
      },
      have v_rest : v = list.join (list.map (++ [H]) (list.map (list.map wrap_sym) x)),
      {
        -- follows from `bef`
        sorry,
      },
      rw aft,
      rw [u_nil, v_rest],
      rw [list.nil_append, list.map_cons],
      refl,
    },
    sorry,
  },
  sorry
end


/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : language T) :
  is_RE L  →  is_RE L.star  :=
begin
  rintro ⟨g, hg⟩,
  use star_grammar g,

  apply set.eq_of_subset_of_subset,
  {
    -- prove `L₁ * L₂ ⊇` here
    intros w hyp,
    unfold grammar_language at hyp,
    rw set.mem_set_of_eq at hyp,
    have result := star_induction hyp,
    cases result,
    {
      exfalso,
      sorry,
    },
    cases result,
    {
      exfalso,
      sorry,
    },
    cases result,
    {
      exfalso,
      sorry,
    },
    cases result,
    {
      rcases result with ⟨u, win, map_eq_map⟩,
      have fuj : function.injective symbol.terminal, sorry,
      rw ←list.map_injective_iff at fuj,
      have w_eq_u : w = u, exact fuj map_eq_map,
      rw [w_eq_u, ←hg],
      exact win,
    },
    cases result,
    {
      exfalso,
      sorry,
    },
    {
      exfalso,
      sorry,
    },
  },
  {
    sorry,
  },
end
