import computability.language

variables {T : Type}

def reverse_lang (L : language T) : language T :=
λ w : list T, w.reverse ∈ L

def bijemap_lang {T' : Type} (L : language T) (π : equiv T T') : language T' :=
λ w : list T', list.map π.inv_fun w ∈ L

def permute_lang (L : language T) (π : equiv.perm T) : language T :=
bijemap_lang L π
