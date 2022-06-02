import computability.language


variables {T : Type} (L : language T)

def reverse_lang : language T :=
λ w : list T, w.reverse ∈ L

def bijemap_lang {T' : Type} (π : equiv T T') : language T' :=
λ w : list T', list.map π.inv_fun w ∈ L

def permute_lang (π : equiv.perm T) : language T :=
bijemap_lang L π
