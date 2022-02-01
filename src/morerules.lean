import data.list
import onerule


-- Definitions

def ruleset := finset production_rule

def transformed (rules : ruleset) (oldWord newWord : string) : Prop :=
∃ r ∈ rules.val, transforms r oldWord newWord
/-
def derives (rules : ruleset) (startWord endWord : string) : Prop :=
startWord = endWord ∨ (∃ intermediate : string,
  transformed rules startWord intermediate ∧ derives rules intermediate endWord)

inductive derives (rules : ruleset) (startWord endWord : string) : Prop
| step_base : startWord = endWord → derives
| step_indu : (∃ intermediate : string,
    transformed rules startWord intermediate ∧ derives rules intermediate endWord) → derives
-/