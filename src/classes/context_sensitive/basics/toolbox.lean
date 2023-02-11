import classes.context_sensitive.basics.definition

variables {T : Type} {g : CS_grammar T}


/-- The relation `CS_derives` is reflexive. -/
lemma CS_deri_self {w : list (symbol T g.nt)} :
  CS_derives g w w :=
relation.refl_trans_gen.refl

lemma CS_deri_of_tran {v w : list (symbol T g.nt)} :
  CS_transforms g v w → CS_derives g v w :=
relation.refl_trans_gen.single

/-- The relation `CS_derives` is transitive. -/
lemma CS_deri_of_deri_deri {u v w : list (symbol T g.nt)}
    (huv : CS_derives g u v) (hvw : CS_derives g v w) :
  CS_derives g u w :=
relation.refl_trans_gen.trans huv hvw

lemma CS_deri_of_deri_tran {u v w : list (symbol T g.nt)}
    (huv : CS_derives g u v) (hvw : CS_transforms g v w) :
  CS_derives g u w :=
CS_deri_of_deri_deri huv (CS_deri_of_tran hvw)

lemma CS_deri_of_tran_deri {u v w : list (symbol T g.nt)}
    (huv : CS_transforms g u v) (hvw : CS_derives g v w) :
  CS_derives g u w :=
CS_deri_of_deri_deri (CS_deri_of_tran huv) hvw

lemma CS_tran_or_id_of_deri {u w : list (symbol T g.nt)} (ass : CS_derives g u w) :
  (u = w) ∨
  (∃ v : list (symbol T g.nt), (CS_transforms g u v) ∧ (CS_derives g v w)) :=
relation.refl_trans_gen.cases_head ass
