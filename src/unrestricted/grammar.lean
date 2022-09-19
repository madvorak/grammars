import logic.relation
import computability.language
import list_append_append


/-- Fundamental datatype; basically `τ ⊕ ν` (something like "Either tau nyy")
    where `τ` is the type of terminals and `ν` is the type of nonterminals. -/
inductive symbol (τ : Type) (ν : Type)
| terminal    : τ → symbol
| nonterminal : ν → symbol


section grammar_definitions

/-- Transformation rule for a grammar without any restrictions. -/
structure grule (τ : Type) (ν : Type) :=
(input_L : list (symbol τ ν))
(input_N : ν)
(input_R : list (symbol τ ν))
(output_string : list (symbol τ ν))

structure frule (τ : Type) (ν : Type) :=
(input_string : list (symbol τ ν))
(marked_nt : ν)
(contains_nt : symbol.nonterminal marked_nt ∈ input_string)
(output_string : list (symbol τ ν))

/-- Grammar (general) that generates words over the alphabet `termi` (a type of terminals). -/
structure grammar (termi : Type) :=
(nt : Type)                     -- type of nonterminals
(initial : nt)                  -- initial symbol
(rules : list (grule termi nt)) -- rewriting rules

structure frammar (termi : Type) :=
(nt : Type)                     -- type of nonterminals
(initial : nt)                  -- initial symbol
(rules : list (frule termi nt)) -- rewriting rules


variables {T : Type}

/-- One step of grammatical transformation. -/
def grammar_transforms (g : grammar T) (w₁ w₂ : list (symbol T g.nt)) : Prop :=
∃ r : grule T g.nt,
  r ∈ g.rules ∧
  ∃ u v : list (symbol T g.nt), and
    (w₁ = u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v)
    (w₂ = u ++ r.output_string ++ v)

def frammar_transforms (g : frammar T) (w₁ w₂ : list (symbol T g.nt)) : Prop :=
∃ r : frule T g.nt,
  r ∈ g.rules ∧
  ∃ u v : list (symbol T g.nt), and
    (w₁ = u ++ r.input_string ++ v)
    (w₂ = u ++ r.output_string ++ v)

/-- Any number of steps of grammatical transformation; reflexive+transitive closure of `grammar_transforms`. -/
def grammar_derives (g : grammar T) : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (grammar_transforms g)

def frammar_derives (g : frammar T) : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (frammar_transforms g)

def grammar_generates (g : grammar T) (w : list T) : Prop :=
grammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

def frammar_generates (g : frammar T) (w : list T) : Prop :=
frammar_derives g [symbol.nonterminal g.initial] (list.map symbol.terminal w)

/-- Returns the set of words (lists of terminals) that can be derived from the initial nonterminal. -/
def grammar_language (g : grammar T) : language T :=
set_of (grammar_generates g)

def frammar_language (g : frammar T) : language T :=
set_of (frammar_generates g)

/-- Predicate "is recursively-enumerable"; defined by an existence of a grammar for the given language. -/
def is_RE (L : language T) : Prop :=
∃ g : grammar T, grammar_language g = L

end grammar_definitions


section grammar_frammar

variables {T : Type}

def frule_of_grule {N : Type} (r : grule T N) : frule T N :=
frule.mk
  (r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R)
  r.input_N
  (by {
    apply list.mem_append_left,
    apply list.mem_append_right,
    apply list.mem_singleton_self,
  })
  r.output_string

def grule_of_frule {N : Type} (r : frule T N) : grule T N :=
let index := /-list.index_of r.marked_nt r.input_string-/ 42
in grule.mk -- TODO
  (list.take index r.input_string)
  r.marked_nt
  (list.drop (index + 1) r.input_string)
  r.output_string

def frammar_of_grammar (g : grammar T) : frammar T :=
frammar.mk g.nt g.initial (list.map frule_of_grule g.rules)

def grammar_of_frammar (g : frammar T) : grammar T :=
grammar.mk g.nt g.initial (list.map grule_of_frule g.rules)

lemma frammar_transforms_of_grammar_transforms (g : grammar T) (w₁ w₂ : list (symbol T g.nt)) :
  grammar_transforms g w₁ w₂  ↔  frammar_transforms (frammar_of_grammar g) w₁ w₂  :=
begin
  split,
  {
    rintro ⟨r, rin, u, v, bef, aft⟩,
    use frule_of_grule r,
    split,
    {
      change frule_of_grule r ∈ (list.map frule_of_grule g.rules),
      rw list.mem_map,
      use r,
      exact ⟨rin, rfl⟩,
    },
    use u,
    use v,
    split,
    {
      repeat {
        rw list.append_assoc at bef,
      },
      rw ←list.append_assoc [symbol.nonterminal r.input_N] _ _ at bef,
      rw ←list.append_assoc r.input_L _ _ at bef,
      rw ←list.append_assoc r.input_L _ _ at bef,
      rw ←list.append_assoc at bef,
      exact bef,
    },
    {
      exact aft,
    },
  },
  {
    rintro ⟨r, rin, u, v, bef, aft⟩,
    use grule_of_frule r,
    sorry,
  },
end

lemma frammar_transforms_of_grammar_transforms' (g : grammar T) :
  grammar_transforms g = frammar_transforms (frammar_of_grammar g) :=
begin
  ext w₁ w₂,
  exact frammar_transforms_of_grammar_transforms g w₁ w₂,
end

lemma frammar_derives_of_grammar_derives' (g : grammar T) :
  grammar_derives g = frammar_derives (frammar_of_grammar g) :=
begin
  unfold grammar_derives,
  rw frammar_transforms_of_grammar_transforms',
  refl,
end

lemma frammar_derives_of_grammar_derives (g : grammar T) (v w : list (symbol T g.nt)) :
  grammar_derives g v w  ↔  frammar_derives (frammar_of_grammar g) v w  :=
begin
  rw frammar_derives_of_grammar_derives' g,
end

end grammar_frammar


section grammar_utilities
variables {T : Type} {g : grammar T}

/-- The relation `grammar_derives` is reflexive. -/
lemma grammar_deri_self {w : list (symbol T g.nt)} :
  grammar_derives g w w :=
relation.refl_trans_gen.refl

lemma grammar_deri_of_tran {v w : list (symbol T g.nt)} :
  grammar_transforms g v w → grammar_derives g v w :=
relation.refl_trans_gen.single

/-- The relation `grammar_derives` is transitive. -/
lemma grammar_deri_of_deri_deri {u v w : list (symbol T g.nt)}
    (huv : grammar_derives g u v) (hvw : grammar_derives g v w) :
  grammar_derives g u w :=
relation.refl_trans_gen.trans huv hvw

lemma grammar_deri_of_deri_tran {u v w : list (symbol T g.nt)}
    (huv : grammar_derives g u v) (hvw : grammar_transforms g v w) :
  grammar_derives g u w :=
grammar_deri_of_deri_deri huv (grammar_deri_of_tran hvw)

lemma grammar_deri_of_tran_deri {u v w : list (symbol T g.nt)}
    (huv : grammar_transforms g u v) (hvw : grammar_derives g v w) :
  grammar_derives g u w :=
grammar_deri_of_deri_deri (grammar_deri_of_tran huv) hvw

lemma grammar_tran_or_id_of_deri {u w : list (symbol T g.nt)} (ass : grammar_derives g u w) :
  (u = w) ∨
  (∃ v : list (symbol T g.nt), (grammar_transforms g u v) ∧ (grammar_derives g v w)) :=
relation.refl_trans_gen.cases_head ass


lemma grammar_derives_with_prefix
    {w₁ w₂ : list (symbol T g.nt)}
    (pᵣ : list (symbol T g.nt))
    (ass : grammar_derives g w₁ w₂) :
  grammar_derives g (pᵣ ++ w₁) (pᵣ ++ w₂) :=
begin
  induction ass with x y trash hyp ih,
  {
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨rule, rule_in, u, v, h_bef, h_aft⟩,
  use rule,
  split,
  {
    exact rule_in,
  },
  use pᵣ ++ u,
  use v,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma grammar_derives_with_postfix
    {w₁ w₂ : list (symbol T g.nt)}
    (pₒ : list (symbol T g.nt))
    (ass : grammar_derives g w₁ w₂) :
  grammar_derives g (w₁ ++ pₒ) (w₂ ++ pₒ) :=
begin
  induction ass with x y trash hyp ih,
  {
    apply grammar_deri_self,
  },
  apply grammar_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨rule, rule_in, u, v, h_bef, h_aft⟩,
  use rule,
  split,
  {
    exact rule_in,
  },
  use u,
  use v ++ pₒ,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma grammar_derives_with_prefix_and_postfix
    {w₁ w₂ : list (symbol T g.nt)}
    (pᵣ pₒ : list (symbol T g.nt))
    (ass : grammar_derives g w₁ w₂) :
  grammar_derives g (pᵣ ++ w₁ ++ pₒ) (pᵣ ++ w₂ ++ pₒ) :=
begin
  apply grammar_derives_with_postfix,
  apply grammar_derives_with_prefix,
  exact ass,
end

end grammar_utilities
