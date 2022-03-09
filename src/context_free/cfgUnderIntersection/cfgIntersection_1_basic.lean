import cfg
import cfgPumping
import tactic


section counting_symbols
variables {α : Type} [decidable_eq α]

def count_in (w : list α) (a : α) : ℕ :=
list.sum (list.map (λ x, ite (x = a) 1 0) w)

lemma count_in_repeat_eq (a : α) (n : ℕ) :
  count_in (list.repeat a n) a  =  n  :=
begin
  sorry,
end

lemma count_in_repeat_neq {a : α} {b : α} (h : a ≠ b) (n : ℕ) :
  count_in (list.repeat a n) b  =  0  :=
begin
  sorry,
end

lemma count_in_append (w₁ w₂ : list α) (a : α) :
  count_in (w₁ ++ w₂) a  =  count_in w₁ a  +  count_in w₂ a  :=
begin
  rw count_in,
  rw list.map_append,
  rw list.sum_append,
  refl,
end

lemma count_in_le_length {w : list α} {a : α} :
  count_in w a ≤ w.length :=
-- maybe not be needed in the end
begin
  rw count_in,
  have upper_bound : ∀ y : α, (λ (x : α), ite (x = a) 1 0) y ≤ 1,
  {
    intro z,
    simp,
    by_cases (z = a),
    {
      rw h,
      simp,
    },
    {
      convert_to ite false 1 0 ≤ 1;
      simp,
      exact h,
    },
  },
  calc (list.map (λ (x : α), ite (x = a) 1 0) w).sum
      ≤ (list.map (λ (x : α), 1) w).sum : sorry
  ... ≤ 1 * w.length                    : sorry
  ... = w.length                        : by rw one_mul,
end

lemma count_in_pos_of_in {w : list α} {a : α} (h : a ∈ w) :
  count_in w a > 0 :=
begin
  by_contradiction contr,
  rw not_lt at contr,
  rw nat.le_zero_iff at contr,
  sorry,
end

lemma count_in_zero_of_notin {w : list α} {a : α} (h : a ∉ w) :
  count_in w a = 0 :=
begin
  sorry,
end

end counting_symbols


def a_ : fin 3 := 0
def b_ : fin 3 := 1
def c_ : fin 3 := 2

def lang_eq_any : language (fin 3) :=
λ w, ∃ n m : ℕ, w = list.repeat a_ n ++ list.repeat b_ n ++ list.repeat c_ m

def lang_any_eq : language (fin 3) :=
λ w, ∃ n m : ℕ, w = list.repeat a_ n ++ list.repeat b_ m ++ list.repeat c_ m

def lang_eq_eq : language (fin 3) :=
λ w, ∃ n : ℕ, w = list.repeat a_ n ++ list.repeat b_ n ++ list.repeat c_ n
