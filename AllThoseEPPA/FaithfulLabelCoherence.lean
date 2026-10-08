import AllThoseEPPA.FaithfulCanonicalCoherence

/-!
# Coherence of faithful label fibres

This file isolates the composition laws for the partial and total label
bijections used in the faithful witness lift.
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- Used source labels depend only on the source set of the partial
automorphism. -/
theorem usedSourceLabels_eq_of_source_eq
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (I : BadIrreducible act A B₀ ψ)
    (hs : p.source = q.source) :
    usedSourceLabels act A B₀ ψ p I =
      usedSourceLabels act A B₀ ψ q I := by
  ext l
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [← hs]
      exact x.2.1
    · apply Subtype.ext
      rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [hs]
      exact x.2.1
    · apply Subtype.ext
      rfl

/-- For a fixed base automorphism, used target labels depend only on the
target set of the partial automorphism. -/
theorem usedTargetLabels_eq_of_target_eq
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (ht : p.target = q.target) :
    usedTargetLabels act A B₀ ψ p g I =
      usedTargetLabels act A B₀ ψ q g I := by
  ext l
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [← ht]
      exact x.2.1
    · apply Subtype.ext
      rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [ht]
      exact x.2.1
    · apply Subtype.ext
      rfl

/-- When the target of one faithful partial automorphism is the source of the
next, the intermediate used-label sets agree literally. -/
theorem usedTargetLabels_eq_usedSourceLabels
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (I : BadIrreducible act A B₀ ψ)
    (ht : p.target = q.source) :
    usedTargetLabels act A B₀ ψ p g I =
      usedSourceLabels act A B₀ ψ q
        (I.transport act A B₀ ψ g) := by
  ext l
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [← ht]
      exact x.2.1
    · apply Subtype.ext
      rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ?_, x.2.2⟩, ?_⟩
    · rw [ht]
      exact x.2.1
    · apply Subtype.ext
      rfl

end Faithful
end AllThoseEPPA
