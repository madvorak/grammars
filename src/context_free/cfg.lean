import unrestricted.grammar


section cfg_definitions

/-- Context-free grammar that generates words over the alphabet `termi` (a type of terminals). -/
structure CF_grammar (T : Type) :=
(nt : Type)                                -- type of nonterminals
(initial : nt)                             -- initial symbol
(rules : list (nt × list (symbol T nt)))   -- rewrite rules


variables {T : Type}

/-- One step of context-free transformation. -/
def CF_transforms (g : CF_grammar T) (w₁ w₂ : list (symbol T g.nt)) : Prop :=
∃ r : g.nt × list (symbol T g.nt), r ∈ g.rules ∧ ∃ u v : list (symbol T g.nt), and
  (w₁ = u ++ [symbol.nonterminal r.fst] ++ v)
  (w₂ = u ++ r.snd ++ v)

/-- Any number of steps of context-free transformation; reflexive+transitive closure of `CF_transforms`. -/
def CF_derives (g : CF_grammar T) : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CF_transforms g)

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def CF_generates (g : CF_grammar T) (w : list T) : Prop :=
CF_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

/-- Context-free language; just a wrapper around `CF_generates`. -/
def CF_language (g : CF_grammar T) : language T :=
set_of (CF_generates g)

/-- Predicate "is context-free"; defined by an existence of a context-free grammar for the given language. -/
def is_CF (L : language T) : Prop :=
∃ g : CF_grammar T, CF_language g = L

end cfg_definitions


section cfg_utilities
variables {T : Type} {g : CF_grammar T}

lemma CF_deri_of_tran {v w : list (symbol T g.nt)} :
  CF_transforms g v w → CF_derives g v w :=
relation.refl_trans_gen.single

/-- The relation `CF_derives` is reflexive. -/
lemma CF_deri_self {w : list (symbol T g.nt)} :
  CF_derives g w w :=
relation.refl_trans_gen.refl

/-- The relation `CF_derives` is transitive. -/
lemma CF_deri_of_deri_deri {u v w : list (symbol T g.nt)}
    (huv : CF_derives g u v)
    (hvw : CF_derives g v w) :
  CF_derives g u w :=
relation.refl_trans_gen.trans huv hvw

lemma CF_deri_of_deri_tran {u v w : list (symbol T g.nt)}
    (huv : CF_derives g u v)
    (hvw : CF_transforms g v w) :
  CF_derives g u w :=
CF_deri_of_deri_deri huv (CF_deri_of_tran hvw)

lemma CF_deri_of_tran_deri {u v w : list (symbol T g.nt)}
    (huv : CF_transforms g u v)
    (hvw : CF_derives g v w) :
  CF_derives g u w :=
CF_deri_of_deri_deri (CF_deri_of_tran huv) hvw

lemma CF_tran_or_id_of_deri {u w : list (symbol T g.nt)} (ass : CF_derives g u w) :
  (u = w) ∨
  (∃ v : list (symbol T g.nt), (CF_transforms g u v) ∧ (CF_derives g v w)) :=
relation.refl_trans_gen.cases_head ass


lemma CF_deri_with_prefix {w₁ w₂ : list (symbol T g.nt)}
    (pᵣ : list (symbol T g.nt))
    (ass : CF_derives g w₁ w₂) :
  CF_derives g (pᵣ ++ w₁) (pᵣ ++ w₂) :=
begin
  induction ass with a b irr hyp ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨rule, rule_in, v, w, h_bef, h_aft⟩,
  use rule,
  split,
  {
    exact rule_in,
  },
  use pᵣ ++ v,
  use w,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma CF_deri_with_postfix {w₁ w₂ : list (symbol T g.nt)}
    (pₒ : list (symbol T g.nt))
    (ass : CF_derives g w₁ w₂) :
  CF_derives g (w₁ ++ pₒ) (w₂ ++ pₒ) :=
begin
  induction ass with a b irr hyp ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨rule, rule_in, v, w, h_bef, h_aft⟩,
  use rule,
  split,
  {
    exact rule_in,
  },
  use v,
  use w ++ pₒ,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma CF_deri_with_prefix_and_postfix {w₁ w₂ : list (symbol T g.nt)}
    (pᵣ pₒ : list (symbol T g.nt))
    (ass : CF_derives g w₁ w₂) :
  CF_derives g (pᵣ ++ w₁ ++ pₒ) (pᵣ ++ w₂ ++ pₒ) :=
begin
  apply CF_deri_with_postfix,
  apply CF_deri_with_prefix,
  exact ass,
end

end cfg_utilities


section cfg_conversion

variables {T : Type}

def grammar_of_cfg (g : CF_grammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map (λ r : g.nt × (list (symbol T g.nt)),
  grule.mk [] r.fst [] r.snd) g.rules)

lemma CF_language_eq_grammar_language (g : CF_grammar T) :
  CF_language g = grammar_language (grammar_of_cfg g) :=
begin
  unfold CF_language grammar_language,
  ext,
  rw [set.mem_set_of_eq, set.mem_set_of_eq],
  unfold CF_generates grammar_generates,
  split;
  intro ass,
  {
    induction ass with x y trash hyp ih,
    {
      apply grammar_deri_self,
    },
    apply grammar_deri_of_deri_tran ih,
    rcases hyp with ⟨r, rin, u, v, bef, aft⟩,
    use grule.mk [] r.fst [] r.snd,
    split,
    {
      delta grammar_of_cfg,
      dsimp only,
      rw list.mem_map,
      exact ⟨r, rin, rfl⟩,
    },
    use [u, v],
    split,
    {
      simp only [list.append_nil],
      exact bef,
    },
    {
      exact aft,
    },
  },
  {
    induction ass with x y trash hyp ih,
    {
      apply CF_deri_self,
    },
    apply CF_deri_of_deri_tran ih,
    rcases hyp with ⟨r, rin, u, v, bef, aft⟩,
    delta grammar_of_cfg at rin,
    rw list.mem_map at rin,
    rcases rin with ⟨r₀, rin₀, eq_r⟩,
    use r₀,
    split,
    {
      exact rin₀,
    },
    use [u, v],
    split,
    {
      rw ←eq_r at bef,
      simpa only [list.append_nil] using bef,
    },
    {
      rw ←eq_r at aft,
      exact aft,
    },
  },
end

theorem CF_subclass_RE {L : language T} :
  is_CF L → is_RE L :=
begin
  rintro ⟨g, eq_L⟩,
  use grammar_of_cfg g,
  rw ←eq_L,
  rw CF_language_eq_grammar_language,
end

end cfg_conversion
