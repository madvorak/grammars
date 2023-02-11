import classes.context_free.basics.toolbox
import utilities.language_operations


variables {T₁ T₂ N : Type}

private def sT₂_of_sT₁ (π : equiv T₁ T₂) : (symbol T₁ N) → (symbol T₂ N)
| (symbol.terminal t) := symbol.terminal (π.to_fun t)
| (symbol.nonterminal n) := symbol.nonterminal n

private def sT₁_of_sT₂ (π : equiv T₁ T₂) : (symbol T₂ N) → (symbol T₁ N)
| (symbol.terminal t) := symbol.terminal (π.inv_fun t)
| (symbol.nonterminal n) := symbol.nonterminal n

private def lsT₂_of_lsT₁ (π : equiv T₁ T₂) : list (symbol T₁ N) → list (symbol T₂ N) :=
list.map (sT₂_of_sT₁ π)

private def lsT₁_of_lsT₂ (π : equiv T₁ T₂) : list (symbol T₂ N) → list (symbol T₁ N) :=
list.map (sT₁_of_sT₂ π)

/-- The class of context-free languages is closed under bijection between terminal alphabets. -/
theorem CF_of_bijemap_CF (π : equiv T₁ T₂) (L : language T₁) :
  is_CF L  →  is_CF (bijemap_lang L π)  :=
begin
  rintro ⟨g, hg⟩,

  let g' : CF_grammar T₂ := CF_grammar.mk g.nt g.initial (list.map (
      λ r : g.nt × (list (symbol T₁ g.nt)), (r.fst, lsT₂_of_lsT₁ π r.snd)
    ) g.rules),
  use g',

  apply set.eq_of_subset_of_subset,
  {
    intros w hw,
    unfold bijemap_lang,
    change list.map π.inv_fun w ∈ L,
    rw ←hg,

    unfold CF_language at hw ⊢,
    rw set.mem_set_of_eq at hw ⊢,
    unfold CF_generates at hw ⊢,
    unfold CF_generates_str at hw ⊢,

    have deri_of_deri :
      ∀ v : list (symbol T₂ g'.nt),
        CF_derives g' [symbol.nonterminal g'.initial] v →
          CF_derives g [symbol.nonterminal g.initial] (lsT₁_of_lsT₂ π v),
    {
      intros v hv,
      induction hv with u v trash orig ih,
      {
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran,
      {
        exact ih,
      },
      rcases orig with ⟨r, r_in, x, y, bef, aft⟩,
      let r₁ := (r.fst, lsT₁_of_lsT₂ π r.snd),
      let x₁ := lsT₁_of_lsT₂ π x,
      let y₁ := lsT₁_of_lsT₂ π y,
      use r₁,
      split,
      {
        change (r.fst, lsT₁_of_lsT₂ π r.snd) ∈ g.rules,
        rw [list.mem_map, prod.exists] at r_in,
        rcases r_in with ⟨a, b, ab_in, ab_eq⟩,
        have a_eq : a = r.fst :=
          (congr_arg prod.fst ab_eq).congr_right.mp rfl,
        have b_eq : lsT₂_of_lsT₁ π b = r.snd :=
          (congr_arg prod.snd ab_eq).congr_right.mp rfl,
        rw a_eq at ab_in,
        convert ab_in,
        rw ←b_eq,
        unfold lsT₁_of_lsT₂,
        unfold lsT₂_of_lsT₁,
        rw list.map_map,
        ext1,
        rw list.nth_map,
        cases (b.nth n),
        {
          -- none = none
          refl,
        },
        cases val, swap,
        {
          -- nonterminal = nonterminal
          refl,
        },
        {
          -- (sT₁_of_sT₂ π ∘ sT₂_of_sT₁ π) terminal = terminal
          simp [sT₂_of_sT₁, sT₁_of_sT₂, equiv.left_inv],
        }
      },
      use x₁,
      use y₁,
      split,
      {
        rw bef,
        unfold lsT₁_of_lsT₂,
        rw list.map_append,
        rw list.map_append,
        refl,
      },
      {
        rw aft,
        unfold lsT₁_of_lsT₂,
        rw list.map_append,
        rw list.map_append,
        refl,
      },
    },
    specialize deri_of_deri (list.map symbol.terminal w) hw,
    unfold lsT₁_of_lsT₂ at deri_of_deri,
    rw list.map_map at *,
    convert deri_of_deri,
  },
  {
    intros w hw,
    unfold bijemap_lang at hw,
    change list.map π.inv_fun w ∈ L at hw,
    rw ←hg at hw,
    unfold CF_language at hw,
    rw set.mem_set_of_eq at hw,
    unfold CF_generates at hw,
    rw list.map_map at hw,
    unfold CF_generates_str at hw,

    unfold CF_language,
    change CF_generates_str g' (list.map symbol.terminal w),
    unfold CF_generates_str,

    have deri_of_deri :
      ∀ v : list (symbol T₁ g.nt),
        CF_derives g [symbol.nonterminal g.initial] v →
          CF_derives g' [symbol.nonterminal g'.initial] (lsT₂_of_lsT₁ π v),
    {
      intros v hv,
      induction hv with u v trash orig ih,
      {
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran,
      {
        exact ih,
      },
      rcases orig with ⟨r, r_in, x, y, bef, aft⟩,
      let r₂ := (r.fst, lsT₂_of_lsT₁ π r.snd),
      let x₂ := lsT₂_of_lsT₁ π x,
      let y₂ := lsT₂_of_lsT₁ π y,
      use r₂,
      split,
      {
        rw [list.mem_map, prod.exists],
        use r.fst,
        use r.snd,
        split,
        {
          convert r_in,
          exact prod.ext rfl rfl,
        },
        split;
        refl,
      },
      use x₂,
      use y₂,
      split,
      {
        rw bef,
        unfold lsT₂_of_lsT₁,
        rw list.map_append,
        rw list.map_append,
        refl,
      },
      {
        rw aft,
        unfold lsT₂_of_lsT₁,
        rw list.map_append,
        rw list.map_append,
        refl,
      },
    },
    specialize deri_of_deri (list.map (symbol.terminal ∘ π.inv_fun) w) hw,
    rw lsT₂_of_lsT₁ at deri_of_deri,
    rw list.map_map at deri_of_deri,
    convert deri_of_deri,
    ext1,
    change symbol.terminal x = sT₂_of_sT₁ π (symbol.terminal (π.inv_fun x)),
    unfold sT₂_of_sT₁,
    rw equiv.right_inv,
  },
end
