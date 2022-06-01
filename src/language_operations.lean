import computability.language


variables {T : Type}

def reverse_lang (L : language T) : language T :=
λ w : list T, w.reverse ∈ L

def bijemap_lang {T' : Type} (π : equiv T T') (L : language T) : language T' :=
λ w : list T', list.map π.inv_fun w ∈ L

def permute_lang (π : equiv.perm T) (L : language T) : language T :=
bijemap_lang π L
