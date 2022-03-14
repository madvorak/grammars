import logic.relation
import computability.language


section cfg_main

/-- Fundamental datatype; basically `τ ⊕ ν` (something like "Either tau nyy")
    where `τ` is the type of terminals and `ν` is the type of nonterminals. -/
inductive symbol (τ : Type) (ν : Type)
| terminal    : τ → symbol
| nonterminal : ν → symbol

/-- Context-free grammar that generates words over the alphabet `termi` (a type of terminals). -/
structure CF_grammar (termi : Type) :=
(nt : Type)                                      -- type of nonterminals
(initial : nt)                                   -- initial symbol
(rules : list (nt × (list (symbol termi nt))))   -- rewriting rules

end cfg_main


section cfg_derivations
variables {T : Type} (g : CF_grammar T)

/-- One step of context-free transformation. -/
def CF_transforms (oldWord newWord : list (symbol T g.nt)) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbol T g.nt), 
  oldWord = v ++ [symbol.nonterminal (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

/-- Any number of steps of context-free transformation; reflexive+transitive closure of `CF_transforms`. -/
def CF_derives : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CF_transforms g)

/-- Accepts a list of symbols iff it can be derived from the initial nonterminal. -/
def CF_generates_str (str : list (symbol T g.nt)) : Prop :=
CF_derives g [symbol.nonterminal g.initial] str

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def CF_generates (word : list T) : Prop :=
CF_generates_str g (list.map symbol.terminal word)

end cfg_derivations


section cfg_languages
variable {T : Type}

/-- Context free language; just a wrapper around `CF_generates`.  -/
def CF_language (g : CF_grammar T) : language T :=
CF_generates g

/-- Predicate "is context-free"; defined by an existence of a context-free grammar for given language. -/
def is_CF (L : language T) :=
∃ g : CF_grammar T, CF_language g = L


/-- Context-free grammar for the empty language (i.e., `∈` always gives `false`). -/
def cfg_empty_lang : CF_grammar T :=
CF_grammar.mk (fin 1) 0 []

/-- Context-free grammar for the singleton language that contains `[]` as its only word. -/
def cfg_empty_word : CF_grammar T :=
CF_grammar.mk (fin 1) 0 [(0, [])]

/-- Context-free grammar for a language `{a}.star` where `a` is a given terminal symbol. -/
def cfg_symbol_star (a : T) : CF_grammar T :=
CF_grammar.mk (fin 1) 0 [(0, [symbol.terminal a, symbol.nonterminal 0]), (0, [])]

end cfg_languages


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
  (huv : CF_derives g u v) (hvw : CF_derives g v w) :
    CF_derives g u w :=
relation.refl_trans_gen.trans huv hvw

lemma CF_deri_of_deri_tran {u v w : list (symbol T g.nt)}
  (huv : CF_derives g u v) (hvw : CF_transforms g v w) :
    CF_derives g u w :=
CF_deri_of_deri_deri huv (CF_deri_of_tran hvw)

lemma CF_deri_of_tran_deri {u v w : list (symbol T g.nt)}
  (huv : CF_transforms g u v) (hvw : CF_derives g v w) :
    CF_derives g u w :=
CF_deri_of_deri_deri (CF_deri_of_tran huv) hvw

lemma CF_tran_or_id_of_deri {u w : list (symbol T g.nt)}
  (h : CF_derives g u w) :  or  (u = w)
    (∃ v : list (symbol T g.nt), (CF_transforms g u v) ∧ (CF_derives g v w)) :=
relation.refl_trans_gen.cases_head h


lemma CF_derives_with_prefix {oldWord newWord : list (symbol T g.nt)}
  (prefi : list (symbol T g.nt)) (h : CF_derives g oldWord newWord) :
    CF_derives g (prefi ++ oldWord) (prefi ++ newWord) :=
begin
  induction h with a b irr hyp ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },

  cases hyp with rule foo,
  cases foo with rule_in bar,
  cases bar with v baz,
  cases baz with w ass,
  cases ass with h_bef h_aft,
  use rule,
  split,
  {
    exact rule_in,
  },

  use prefi ++ v,
  use w,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma CF_derives_with_postfix {oldWord newWord : list (symbol T g.nt)}
  (posfi : list (symbol T g.nt)) (h : CF_derives g oldWord newWord) :
    CF_derives g (oldWord ++ posfi) (newWord ++ posfi) :=
begin
  induction h with a b irr hyp ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },

  cases hyp with rule foo,
  cases foo with rule_in bar,
  cases bar with v baz,
  cases baz with w ass,
  cases ass with h_bef h_aft,
  use rule,
  split,
  {
    exact rule_in,
  },

  use v,
  use w ++ posfi,
  rw h_bef,
  rw h_aft,
  split;
  simp only [list.append_assoc],
end

lemma CF_derives_with_prefix_and_postfix {oldWord newWord : list (symbol T g.nt)}
  (prefi posfi : list (symbol T g.nt)) (h : CF_derives g oldWord newWord) :
    CF_derives g (prefi ++ oldWord ++ posfi) (prefi ++ newWord ++ posfi) :=
begin
  apply CF_derives_with_postfix,
  apply CF_derives_with_prefix,
  exact h,
end

end cfg_utilities
