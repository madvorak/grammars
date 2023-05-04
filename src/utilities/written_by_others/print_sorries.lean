-- Written by Floris van Doorn. BSD license applies.

import tactic.core
import data.bool.basic

namespace tactic

private meta structure find_all_expr_data :=
(matching_subexpr : bool)
(test_passed : bool)
(descendants : list (name × bool × name_set))
(name_map : name_map bool)
(direct_descendants : name_set)

private meta def find_all_exprs_aux (env : environment) (f : expr → bool) (g : name → bool) : name →
  find_all_expr_data → tactic find_all_expr_data
| n ⟨b₀, b₁, l, ns, desc⟩ :=
  match ns.find n with
  | some b := pure ⟨b₀, b || b₁, l, ns, if b then desc.insert n else desc⟩
  | none := if g n then pure ⟨b₀, b₁, l, ns.insert n ff, desc⟩ else do
    d ← env.get n,
    let process (v : expr) : tactic find_all_expr_data :=
      v.mfold ⟨ff, ff, l, ns, mk_name_set⟩ $ λ e _ p,
        if f e then pure ⟨tt, tt, p.descendants, p.name_map, p.direct_descendants⟩ else
        if e.is_constant then find_all_exprs_aux e.const_name p else pure p,
    ⟨b', b, l, ns, desc'⟩ ← process d.value,
    pure ⟨b₀, b₁ || b, if b then (n, b', desc')::l else l, ns.insert n b,
      if b then desc.insert n else desc⟩
  end

private meta def find_all_exprs (env : environment) (test : expr → bool) (exclude : name → bool)
  (nm : name) : tactic $ list $ name × bool × name_set := do
  ⟨_, _, l, _, _⟩ ← find_all_exprs_aux env test exclude nm ⟨ff, ff, [], mk_name_map, mk_name_set⟩,
  pure l

private meta def print_sorries_in (nm : name) (ignore_mathlib := tt) : tactic unit := do
  env ← get_env,
  dir ← get_mathlib_dir,
  data ← find_all_exprs env (λ e, e.is_sorry.is_some)
    (if ignore_mathlib then env.is_prefix_of_file dir else λ _, ff) nm,
  let to_print : list format := data.map $ λ ⟨nm, contains_sorry, desc⟩,
    let s1 := if contains_sorry then " CONTAINS SORRY" else "",
        s2 := if contains_sorry && !desc.empty then " and" else "",
        s3 := string.join $ (desc.to_list.map to_string).intersperse ", ",
        s4 := if !desc.empty then format!" depends on {s3}" else "" in
    format!"{nm}{s1}{s2}{s4}.",
  trace $ format.join $ to_print.intersperse format.line

setup_tactic_parser

@[user_command]
meta def print_sorries_in_cmd (_ : parse $ tk "#print_sorries_in") : parser unit := do
  nm ← ident,
  nm ← resolve_name nm,
  print_sorries_in nm.const_name

end tactic
