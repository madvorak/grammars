import context_free.cfgUnderUnion.cfgUnion_1_basic
import context_free.cfgUnderUnion.cfgUnion_2_subset
import context_free.cfgUnderUnion.cfgUnion_3_supset

namespace cfg_union

/-- The class of context-free languages is closed under union. -/
theorem CF_of_CF_u_CF {T : Type} (L₁ : language T) (L₂ : language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ + L₂)   :=
begin
  intro input,
  cases input with cf₁ cf₂,
  cases cf₁ with g₁ h₁,
  cases cf₂ with g₂ h₂,

  use union_grammar g₁ g₂,

  apply set.eq_of_subset_of_subset,
  {
    -- prove `L₁ + L₂ ⊇ `
    intros w hyp,
    simp,
    rw ← h₁,
    rw ← h₂,
    exact in_language_of_in_union w hyp,
  },
  {
    -- prove `L₁ + L₂ ⊆ `
    intros w hyp,
    rw language.mem_add at hyp,
    cases hyp with case₁ case₂,
    {
      rw ← h₁ at case₁,
      exact in_union_of_in_first w case₁,
    },
    {
      rw ← h₂ at case₂,
      exact in_union_of_in_second w case₂,
    },
  }
end

end cfg_union
