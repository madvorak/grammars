import unrestricted.grammar


structure conjrule (τ : Type) (ν : Type) :=
(input_nt : ν)
(output_strings : list (list (symbol τ ν)))

/-- Conjunctive grammar that generates words over the alphabet `termi` (a type of terminals). -/
structure CJ_grammar (termi : Type) :=
(nt : Type)
(initial : nt)
(rules : list (conjrule termi nt))

variables {T : Type} (g : CJ_grammar T)

def try_apply_at (r : conjrule T g.nt) (w : list (symbol T g.nt)) (n : ℕ) :
  list (list (symbol T g.nt)) :=
[] -- if w.nth n = some (symbol.nonterminal r.input_nt) then ? else ?? -- TODO

def try_apply_at' (r : conjrule T g.nt) (w : list (symbol T g.nt)) (n : ℕ) (hn : n < w.length) :
  list (list (symbol T g.nt)) :=
[] -- if w.nth_le n hn = symbol.nonterminal r.input_nt then ? else ?? -- TODO

def conjrule_apply (r : conjrule T g.nt) (w : list (symbol T g.nt)) : list (list (list (symbol T g.nt))) :=
list.filter (λ lis, lis.length > 0) (list.map (λ i, try_apply_at g r w i) (list.range w.length))
