import logic.relation
import tactic
import computability.language


--def is_terminal {alphabet : Type} (x : alphabet) : alphabet → Prop

--variable {alphabet : Type}

structure CF_grammar (alphabet : Type) :=
(is_terminal : alphabet → Prop)
(initial : {x : alphabet // ¬ is_terminal x})
(rules : list ({x : alphabet // ¬ is_terminal x} × list alphabet))

variables {alphabet : Type} {is_terminal : alphabet → Prop}

def terminal := {x : alphabet // is_terminal x}

def nonterminal := {x : alphabet // ¬ is_terminal x}

def CF_transforms (gr : CF_grammar alphabet) (oldWord newWord : list alphabet) : Prop :=
∃ r ∈ gr.rules, ∃ v w : list alphabet, 
  oldWord = v ++ [subtype.val (prod.fst r)] ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def CF_derives (gr : CF_grammar alphabet) := relation.refl_trans_gen (CF_transforms gr)
/-
def CF_generates (gr : CF_grammar alphabet) (word : list terminal) : Prop :=
CF_derives gr [subtype.val gr.initial] (list.map subtype.val word)

def CF_language (gr : CF_grammar alphabet) : language terminal :=
CF_generates gr
-/
def CF_generates (gr : CF_grammar alphabet) (word : list alphabet) : Prop :=
CF_derives gr [subtype.val gr.initial] word

def CF_language (gr : CF_grammar alphabet) : language alphabet :=
CF_generates gr
