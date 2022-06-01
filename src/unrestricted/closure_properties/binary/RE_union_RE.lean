import unrestricted.grammarLiftSink









/-- The class of recursively-enumerable languages is closed under union. -/
theorem RE_of_RE_u_RE {T : Type} (L₁ : language T) (L₂ : language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ + L₂)   :=
begin
  rintro ⟨ ⟨ g₁, h₁ ⟩, ⟨ g₂, h₂ ⟩ ⟩,
  sorry,
end
