import computability.language

def reverse_language {T : Type} (L : language T) : language T :=
λ w : list T, w.reverse ∈ L
