import classes.general.basics.definition

namespace grammars

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

lemma grammar_tran_or_id_of_deri {u w : list (symbol T g.nt)} (huw : grammar_derives g u w) :
  (u = w) ∨
  (∃ v : list (symbol T g.nt), (grammar_transforms g u v) ∧ (grammar_derives g v w)) :=
relation.refl_trans_gen.cases_head huw


lemma grammar_deri_with_prefix {w₁ w₂ : list (symbol T g.nt)}
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
  rcases hyp with ⟨r, rin, u, v, h_bef, h_aft⟩,
  use r,
  split,
  {
    exact rin,
  },
  use [pᵣ ++ u, v],
  rw [h_bef, h_aft],
  split;
  simp only [list.append_assoc],
end

lemma grammar_deri_with_postfix {w₁ w₂ : list (symbol T g.nt)}
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
  rcases hyp with ⟨r, rin, u, v, h_bef, h_aft⟩,
  use r,
  split,
  {
    exact rin,
  },
  use [u, v ++ pₒ],
  rw [h_bef, h_aft],
  split;
  simp only [list.append_assoc],
end


def as_terminal {N : Type} : symbol T N → option T
| (symbol.terminal t)    := some t
| (symbol.nonterminal _) := none

def all_used_terminals (g : grammar T) : list T :=
list.filter_map as_terminal (list.join (list.map grule.output_string g.rules))

end grammars
