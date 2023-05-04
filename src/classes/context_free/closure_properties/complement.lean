import classes.context_free.closure_properties.union
import classes.context_free.closure_properties.intersection

namespace grammars

/-- The class of context-free languages isn't closed under complement. -/
theorem nnyCF_of_complement_CF : ¬ (∀ T : Type, ∀ L : language T,
    is_CF L  →  is_CF (Lᶜ)
) :=
begin
  intro h,
  have nny := nnyCF_of_CF_i_CF,
  push_neg at nny,
  rcases nny with ⟨T, L₁, L₂, ⟨hL₁, hL₂⟩, hyp_neg⟩,
  specialize h T,
  have hu := CF_of_CF_u_CF (L₁ᶜ) (L₂ᶜ) ⟨h L₁ hL₁, h L₂ hL₂⟩,
  have contra := h (L₁ᶜ + L₂ᶜ) hu,
  apply hyp_neg,
  -- golfed by Eric Wieser
  rwa [language.add_def, set.compl_union, compl_compl, compl_compl] at contra,
end

end grammars
