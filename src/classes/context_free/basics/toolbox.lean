import classes.context_free.basics.definition

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
  rcases hyp with ⟨r, r_in, v, w, h_bef, h_aft⟩,
  use r,
  split,
  {
    exact r_in,
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
  rcases hyp with ⟨r, r_in, v, w, h_bef, h_aft⟩,
  use r,
  split,
  {
    exact r_in,
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
