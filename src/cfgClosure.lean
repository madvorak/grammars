import cfg
import computability.DFA
import tactic


def is_Reg {T : Type} (L : language T) :=
∃ σ : Type, ∃ a : DFA T σ, a.accepts = L



theorem CF_intersection_Reg {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
  is_CF L₁ ∧ is_Reg L₂ → is_CF (set.inter L₁ L₂) :=
sorry


theorem CF_under_concatenation {T : Type} [T_fin : fintype T] (L₁ : language T) (L₂ : language T) :
  is_CF L₁ ∧ is_CF L₂ → is_CF (L₁ * L₂) :=
sorry
