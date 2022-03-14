import cfg

-- TODO maybe generalize it to bijections between types (two (possibly different) terminal alphabets)


variable {T : Type}

def permute_lang (π : equiv.perm T) (L : language T) : language T :=
λ w : list T, list.map π.inv_fun w ∈ L

/-- The class of context-free languages is closed under permutation of terminals. -/
theorem CF_of_permute_CF (π : equiv.perm T) (L : language T) :
  is_CF L  →  is_CF (permute_lang π L)  :=
begin
  rintro ⟨ g, hg ⟩,

  let g' : CF_grammar T := CF_grammar.mk
    g.nt
    g.initial
    (list.map
      (λ r : g.nt × (list (symbol T g.nt)), (r.fst, list.map
        (λ s : symbol T g.nt, match s with
          | symbol.terminal ter := symbol.terminal (π.to_fun ter) -- Or should we call `π.inv_fun` instead?
          | symbol.nonterminal nonter := symbol.nonterminal nonter
        end)
      r.snd))
    g.rules),
  use g',
  
  apply set.eq_of_subset_of_subset,
  {
    intros w hw,
    unfold CF_language at hw,
    change CF_generates_str g' (list.map symbol.terminal w) at hw,
    unfold CF_generates_str at hw,
    induction hw,
    {
      
      sorry,
    },
    exact hw_ih, -- This shouldn't work. Maybe the induction is called in a wrong way?
    --sorry,
  },
  {
    intros w hw,
    
    sorry,
  },
end
