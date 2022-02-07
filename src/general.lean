import logic.relation
import tactic
import computability.language


-- TODO require `is_terminal` to be `decidable`

structure grammar (alphabet : Type) :=
(is_terminal : alphabet → Prop)
(initial : {s : alphabet // ¬ is_terminal s})
(rules : list ({x : list alphabet // ∃ a ∈ x, ¬ is_terminal a} × list alphabet))


structure noncontracting (alphabet : Type) extends grammar alphabet :=
(len_non_decr : ∀ r : ({x : list alphabet // ∃ a ∈ x, ¬ is_terminal a} × list alphabet), r ∈ rules →
  r.fst.val.length ≤ r.snd.length)

structure noncontracting_with_empty_word (alphabet : Type) extends grammar alphabet :=
(len_non_decr_or_S_eps : ∀ r : ({x : list alphabet // ∃ a ∈ x, ¬ is_terminal a} × list alphabet), r ∈ rules →
  (r.fst.val.length ≤ r.snd.length ∧ ∀ a : alphabet, a ∈ r.snd → a ≠ initial) ∨ (r.fst.val = [initial] ∧ r.snd = []))


variables {alphabet : Type} {is_terminal : alphabet → Prop}

def grammar_transforms (gr : grammar alphabet) (oldWord newWord : list alphabet) : Prop :=
∃ r ∈ gr.rules, ∃ v w : list alphabet, 
  oldWord = v ++ (subtype.val (prod.fst r)) ++ w ∧ newWord = v ++ (prod.snd r) ++ w

def CF_derives (gr : grammar alphabet) := relation.refl_trans_gen (grammar_transforms gr)
/-
def CF_generates (gr : grammar alphabet) (word : list {a : alphabet // is_terminal a}) : Prop :=
CF_derives gr [subtype.val gr.initial] word ∧ (list.all word (λ a : alphabet, is_terminal a))

def CF_language (gr : grammar alphabet) : language {a : alphabet // is_terminal a} :=
CF_generates gr
-/
def CF_generates (gr : grammar alphabet) (word : list alphabet) : Prop :=
CF_derives gr [subtype.val gr.initial] word

def CF_language (gr : grammar alphabet) : language alphabet :=
CF_generates gr
