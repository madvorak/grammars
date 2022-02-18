import cfg
import computability.DFA
import tactic


def is_Reg {T : Type} (L : language T) :=
∃ σ : Type, ∃ a : DFA T σ, a.accepts = L

def is_CF {T : Type} (L : language T) :=
∃ g : CF_grammar T, CF_language g = L



lemma CF_derives_reflexive {T : Type} {g : CF_grammar T} {w : list (symbol T g.nt)} :
  CF_derives g w w :=
relation.refl_trans_gen.refl

lemma list_three_parts {T₁ T₂ : Type} {x y z : list T₁} {f : T₁ → T₂} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by simp

lemma unpack_transitive_closure {α : Type} {r : α → α → Prop} {x z : α}
  (h : relation.refl_trans_gen r x z) (nontriv : x ≠ z) :
    ∃ y : α, (r x y) ∧ (relation.refl_trans_gen r y z) :=
(relation.refl_trans_gen.cases_head h).resolve_left nontriv
