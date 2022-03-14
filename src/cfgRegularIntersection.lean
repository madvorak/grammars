import cfg
import computability.DFA
import tactic


variable {T : Type}

def is_Reg (L : language T) :=
∃ σ : Type, ∃ a : DFA T σ, a.accepts = L

/-- The class of context-free languages is closed under intersection with regular languages. -/
theorem CF_of_CF_i_Reg (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_Reg L₂   →   is_CF (L₁ ⊓ L₂)   :=
sorry
