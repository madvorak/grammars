import cfgClosureUnion
import cfgClosureIntersection


/-- The class of context-free languages isn't closed under complement. -/
theorem nnyCF_of_complement_CF : ¬ (∀ T : Type, ∀ L : language T,
    is_CF L  →  is_CF (Lᶜ)
) :=
begin
  intro h,
  have nny := nnyCF_of_CF_i_CF,
  push_neg at nny,
  cases nny with T nny_,
  specialize h T,
  cases nny_ with L₁ nny__,
  cases nny__ with L₂ nny_hyp,
  cases nny_hyp with hyp_pos hyp_neg,
  cases hyp_pos with hL₁ hL₂,
  have h₁ := h L₁ hL₁,
  have h₂ := h L₂ hL₂,
  have hu := CF_of_CF_u_CF (L₁ᶜ) (L₂ᶜ) (and.intro h₁ h₂),
  have hnu := h ((L₁ᶜ) + (L₂ᶜ)),
  have contra := hnu hu,
  apply hyp_neg,
  convert contra,
  apply set.eq_of_subset_of_subset;
  intro v;
  intro hv,
  {
    cases hv with hv₁ hv₂,
    intro hvw,
    cases hvw,
    {
      exact hvw hv₁,
    },
    {
      exact hvw hv₂,
    },
  },
  {
    by_cases c₁ : v ∈ L₁,
    by_cases c₂ : v ∈ L₂,
    {
      exact and.intro c₁ c₂,
    },
    {
      exfalso,
      apply hv,
      right,
      exact c₂,
    },
    {
      exfalso,
      apply hv,
      left,
      exact c₁,
    },
  },
end
