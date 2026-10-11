import AllThoseEPPA.IntegerMetricEPPA

/-!
# External-consumer API smoke tests

This module imports ONLY the public facade (not the general EPPA
internals). It verifies how a separate project can unpack the
finite witness, extract an extension of an arbitrary subset
isometry, and use the clique-number equality.
-/

namespace AllThoseEPPA.IntegerMetric.PublicAPIUsage

universe u

/-- A small client of the stronger API: forget the embedding and
extension data after obtaining a witness with the same unit clique
number. -/
theorem findWitnessWithSameCliqueNumber
    (D : ℕ) {α : Type u} [Finite α]
    (A : BoundedNatMetric D α) :
    ∃ (β : Type u) (_ : Finite β)
      (B : BoundedNatMetric D β),
      maximumUnitCliqueSize B = maximumUnitCliqueSize A := by
  obtain ⟨β, hβ, B, _ι, _hIso, _hExt, hClique⟩ :=
    eppaPreservingUnitCliqueNumber D A
  exact ⟨β, hβ, B, hClique⟩

/-- Client example: take a **particular** partial isometry on A
and obtain an actual extending isometry of the witness, while
retaining the unit-clique-number equality. -/
theorem extendGivenPartialIsometry
    (D : ℕ) {α : Type u} [Finite α]
    (A : BoundedNatMetric D α)
    (U V : Set α) (p : U ≃ V)
    (hp : ∀ x y : U,
      A.dist x.1 y.1 = A.dist (p x).1 (p y).1) :
    ∃ (β : Type u) (_ : Finite β)
      (B : BoundedNatMetric D β) (ι : α ↪ β)
      (g : Equiv.Perm β),
      (∀ x y : α, B.dist (ι x) (ι y) = A.dist x y) ∧
      (∀ x y : β, B.dist (g x) (g y) = B.dist x y) ∧
      (∀ x : U, g (ι x.1) = ι (p x).1) ∧
      maximumUnitCliqueSize B = maximumUnitCliqueSize A := by
  obtain ⟨β, hβ, B, ι, hIso, hExt, hClique⟩ :=
    eppaPreservingUnitCliqueNumber D A
  obtain ⟨g, hgIso, hgExt⟩ := hExt U V p hp
  exact ⟨β, hβ, B, ι, g, hIso, hgIso, hgExt, hClique⟩

/-- The ordinary EPPA entry point is available via the same import. -/
theorem ordinaryEPPA
    (D : ℕ) :
    FiniteBoundedMetricsHaveEPPA.{u} D := by
  intro α hFinite A
  exact eppa D A

end AllThoseEPPA.IntegerMetric.PublicAPIUsage
