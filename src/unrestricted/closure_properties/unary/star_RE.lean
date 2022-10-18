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
  (grule.mk  -- `Z → ZS#`
    [] (sum.inr 0) [] [Z, S, H]) ::
  (grule.mk  -- `Z → R#`
    [] (sum.inr 0) [] [R, H]) ::
  (grule.mk  -- `R# → R`
    [] (sum.inr 2) [H] [R]) ::
  (grule.mk  -- `R# → ∅`
    [] (sum.inr 0) [] []) ::
  list.map wrap_gr g.rules ++
  rules_that_scan_terminals g
)


private lemma lemma2 {g : grammar T} {w : list (ns T g.nt)}
    (ass : grammar_derives (star_grammar g) [Z] w) :
  (∃ x : list (list (ns T g.nt)),
    (∀ xᵢ ∈ x, ∃ yᵢ : list (symbol T g.nt),
      grammar_derives g [symbol.nonterminal g.initial] yᵢ ∧ xᵢ = list.map wrap_sym yᵢ) ∧
    (w = Z :: list.join (list.map (++ [H]) x))) ∨
  (∃ x : list (list (ns T g.nt)),
    (∀ xᵢ ∈ x, ∃ yᵢ : list (symbol T g.nt),
      grammar_derives g [symbol.nonterminal g.initial] yᵢ ∧ xᵢ = list.map wrap_sym yᵢ) ∧
    (w = R :: H :: list.join (list.map (++ [H]) x))) ∨
  (∃ w₁ : list (ns T g.nt), sorry) ∨
  (∃ u : list T, u ∈ language.star (grammar_language g) ∧ w = list.map symbol.terminal u) ∨
  (∃ w₀ : list (ns T g.nt), w = w₀ ++ [R]) ∨
  (∃ w₀ : list (ns T g.nt), w = w₀ ++ [H] ∧ Z ∉ w ∧ R ∉ w) :=
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
      use ([S] :: x),
      split,
      {
        intros xᵢ xin,
        cases xin,
        {
          use [[symbol.nonterminal g.initial]],
          split,
          {
            apply grammar_deri_self,
          },
          rw xin,
          refl,
        },
        change xᵢ ∈ x at xin,
        exact valid xᵢ xin,
      },
      have u_nil : u = [],
      {
        -- follows from `bef`
        sorry,
      },
      have v_rest : v = list.join (list.map (++ [H]) x),
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
  rintro ⟨g₀, hg₀⟩,
  use star_grammar g₀,
  sorry,
end
