import logic.relation
import computability.language


section cfg_definitions

inductive symbol (τ : Type) (ν : Type)
| terminal    : τ → symbol
| nonterminal : ν → symbol

structure CF_grammar (termi : Type) :=
(nt : Type)
(initial : nt)
(rules : list (nt × (list (symbol termi nt))))

end cfg_definitions


section cfg_derivations
variables {T : Type} (g : CF_grammar T)

def CF_transforms (oldWord newWord : list (symbol T g.nt)) : Prop :=
∃ r ∈ g.rules, ∃ v w : list (symbol T g.nt), 
  oldWord = v ++ [symbol.nonterminal (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def CF_derives : list (symbol T g.nt) → list (symbol T g.nt) → Prop :=
relation.refl_trans_gen (CF_transforms g)

def CF_generates_str (str : list (symbol T g.nt)) : Prop :=
CF_derives g [symbol.nonterminal g.initial] str

def CF_generates (word : list T) : Prop :=
CF_generates_str g (list.map symbol.terminal word)

end cfg_derivations


section cfg_languages
variable {T : Type}

def CF_language (g : CF_grammar T) : language T :=
CF_generates g

def is_CF (L : language T) :=
∃ g : CF_grammar T, CF_language g = L

end cfg_languages


section cfg_utilities
variables {T : Type} {g : CF_grammar T}

lemma CF_derives_reflexive {w : list (symbol T g.nt)} :
  CF_derives g w w :=
relation.refl_trans_gen.refl

lemma CF_derives_transitive {u w : list (symbol T g.nt)} (v : list (symbol T g.nt))
  (huv : CF_derives g u v) (hvw : CF_derives g v w) :
    CF_derives g u w :=
relation.refl_trans_gen.trans huv hvw

lemma CF_der_of_der_tra {u w : list (symbol T g.nt)} (v : list (symbol T g.nt))
  (huv : CF_derives g u v) (hvw : CF_transforms g v w) :
    CF_derives g u w :=
CF_derives_transitive v huv (relation.refl_trans_gen.single hvw)

lemma CF_der_of_tra_der {u w : list (symbol T g.nt)} (v : list (symbol T g.nt))
  (huv : CF_transforms g u v) (hvw : CF_derives g v w) :
    CF_derives g u w :=
CF_derives_transitive v (relation.refl_trans_gen.single huv) hvw

lemma CF_derives_with_prefix {oldWord newWord : list (symbol T g.nt)}
  (prefi : list (symbol T g.nt)) (h : CF_derives g oldWord newWord) :
    CF_derives g (prefi ++ oldWord) (prefi ++ newWord) :=
begin
  induction h with a b irr hyp ih,
  {
    apply CF_derives_reflexive,
  },
  apply CF_der_of_der_tra (prefi ++ a),
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
    apply CF_derives_reflexive,
  },
  apply CF_der_of_der_tra (a ++ posfi),
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
