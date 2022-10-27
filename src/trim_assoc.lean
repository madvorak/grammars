import tactic
import algebra.group.defs

-- Copyright (c) 2022 Damiano Testa.

private def in_match {α : Type*} [decidable_eq α] : list α → list α → list α
| [] _ := []
| _ [] := []
| (a::as) (b::bs) := if a = b then (a :: in_match as bs) else []

private def split3 {α : Type*} [decidable_eq α] (l r : list α) : list α × (list α × list α) × list α :=
let ini         := in_match l r in
let lx_tail     := l.drop ini.length in
let rx_tail     := r.drop ini.length in
let lx_tail_rev := lx_tail.reverse in
let rx_tail_rev := rx_tail.reverse in
let fin         := (in_match lx_tail_rev rx_tail_rev).reverse in
  (ini,
    ((lx_tail_rev.drop fin.length).reverse,
     (rx_tail_rev.drop fin.length).reverse),
    fin)

private meta def sum_up_with_default {α : Type*} (e : α) (op : α → α → α) : list α → α
| []      := e
| [a]     := a
| (a::as) := as.foldl (λ x y, op x y) a

namespace tactic

private meta def list_binary_operands (f : expr) : expr → tactic (list expr)
| x@(expr.app (expr.app g a) b) := do
  some _ ← try_core (unify f g) | pure [x],
  as ← list_binary_operands a,
  bs ← list_binary_operands b,
  pure (as ++ bs)
| a                             := pure [a]

private meta def assoc_unit (typ : expr) : name → tactic expr
| `has_append.append := to_expr ``([] : %%typ) tt ff
| `has_mul.mul       := to_expr ``(1 : %%typ) tt ff
| `has_add.add       := to_expr ``(0 : %%typ) tt ff
| _ := fail "the tactic does not support this operation"

private meta def assoc_tac : name → tactic unit
| `has_append.append := `[{ simp only [list.append_assoc, list.nil_append, list.append_nil] }]
| `has_mul.mul       := `[{ simp only [mul_assoc, mul_one, one_mul] }]
| `has_add.add       := `[{ simp only [add_assoc, add_zero, zero_add] }]
| _ := fail "the tactic does not support this operation"

meta def interactive.trim : tactic unit := do
`(%%lhs = %%rhs) ← target >>= instantiate_mvars <|> fail "goal is not an equality",
et ← infer_type lhs,
oper ← match lhs with
  | (expr.app (expr.app f _) _) := pure f
  | _ := match rhs with
    | (expr.app (expr.app f _) _) := pure f
    | _ := fail "no operation found"
    end
  end,
opl ← list_binary_operands oper lhs,
opr ← list_binary_operands oper rhs,
let (ini, (ldiff, rdiff), fin) := split3 opl opr,
un ← assoc_unit et oper.get_app_fn.const_name <|> pure lhs,
let rec_l  := [ini, ldiff, fin].map $ sum_up_with_default un (λ x y, oper.mk_app [x, y]),
let rec_r  := [ini, rdiff, fin].map $ sum_up_with_default un (λ x y, oper.mk_app [x, y]),
let nleft  := sum_up_with_default un (λ x y, oper.mk_app [x, y]) rec_l,
let nright := sum_up_with_default un (λ x y, oper.mk_app [x, y]) rec_r,
l_eq ← mk_app `eq [lhs, nleft],
r_eq ← mk_app `eq [nright, rhs],
(_, pr_left)  ← solve_aux l_eq (assoc_tac oper.get_app_fn.const_name),
(_, pr_right) ← solve_aux r_eq (assoc_tac oper.get_app_fn.const_name),
refine ``(eq.trans %%pr_left (eq.trans _ %%pr_right)),
tactic.congr' (some 1),
try $ tactic.congr' (some 1)

add_hint_tactic "trim"

end tactic
