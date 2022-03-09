import cfg
import tactic

namespace cfg_union


lemma list_three_parts {α β : Type} {x y z : list α} {f : α → β} :
  list.map f (x ++ y ++ z) = (list.map f x) ++ (list.map f y) ++ (list.map f z) :=
by simp only [list.map_append]


variables {T : Type} {g₁ g₂ : CF_grammar T}

def sTN_of_sTN₁ : (symbol T g₁.nt) → (symbol T (option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inl snt)))

def sTN_of_sTN₂ : (symbol T g₂.nt) → (symbol T (option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) := (symbol.terminal st)
| (symbol.nonterminal snt) := (symbol.nonterminal (some (sum.inr snt)))

def lsTN_of_lsTN₁ : list (symbol T g₁.nt) → list (symbol T (option (g₁.nt ⊕ g₂.nt))) :=
list.map sTN_of_sTN₁

def lsTN_of_lsTN₂ : list (symbol T g₂.nt) → list (symbol T (option (g₁.nt ⊕ g₂.nt))) :=
list.map sTN_of_sTN₂

def rule_of_rule₁ (r : g₁.nt × (list (symbol T g₁.nt))) :
  ((option (g₁.nt ⊕ g₂.nt)) × (list (symbol T (option (g₁.nt ⊕ g₂.nt))))) :=
(some (sum.inl (prod.fst r)), lsTN_of_lsTN₁ (prod.snd r))

def rule_of_rule₂ (r : g₂.nt × (list (symbol T g₂.nt))) :
  ((option (g₁.nt ⊕ g₂.nt)) × (list (symbol T (option (g₁.nt ⊕ g₂.nt))))) :=
(some (sum.inr (prod.fst r)), lsTN_of_lsTN₂ (prod.snd r))

def union_grammar (gₗ gᵣ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (option (gₗ.nt ⊕ gᵣ.nt)) none (
  (none, [symbol.nonterminal (some (sum.inl (gₗ.initial)))]) ::
  (none, [symbol.nonterminal (some (sum.inr (gᵣ.initial)))]) ::
  ((list.map rule_of_rule₁ gₗ.rules) ++ (list.map rule_of_rule₂ gᵣ.rules))
)

end cfg_union
