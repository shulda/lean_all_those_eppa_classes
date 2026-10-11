import AllThoseEPPA.Examples.IntegerMetricRealRounding
import Mathlib.Topology.MetricSpace.Gluing

/-!
# The empty-interface case of bounded integer metric amalgamation

Use Mathlib's real metric on the disjoint union of two metric
spaces, which is isometric on each summand. Ceiling plus truncation
at D preserves all original integer distances exactly.

This fills the empty amalgamation-base case omitted by the
nonempty-interface Metric.GlueSpace construction. The two
distinguished embeddings have disjoint images, even after
discretization, because discretization changes only distances,
not the vertices of the disjoint union.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u v

theorem finiteDisjointAmalgam_viaRealSum
    {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y]
    [Finite X] [Finite Y]
    (D : ℕ) (hD : 0 < D)
    (MX : BoundedNatMetric D X)
    (MY : BoundedNatMetric D Y)
    (hX : ∀ x y : X, dist x y = (MX.dist x y : ℝ))
    (hY : ∀ x y : Y, dist x y = (MY.dist x y : ℝ)) :
    ∃ (W : Type (max u v)) (_ : Finite W)
      (M : BoundedNatMetric D W)
      (ιX : X → W) (ιY : Y → W),
      (∀ x y : X, M.dist (ιX x) (ιX y) = MX.dist x y) ∧
      (∀ x y : Y, M.dist (ιY x) (ιY y) = MY.dist x y) ∧
      (∀ x : X, ∀ y : Y, ιX x ≠ ιY y) := by
  classical
  letI : MetricSpace (X ⊕ Y) := Metric.metricSpaceSum
  let M : BoundedNatMetric D (X ⊕ Y) :=
    realMetricRounded D hD
  refine ⟨X ⊕ Y, inferInstance, M, Sum.inl, Sum.inr, ?_, ?_, ?_⟩
  · intro x y
    apply realMetricRounded_dist_of_integer D hD
      (Sum.inl x : X ⊕ Y) (Sum.inl y) (MX.dist x y)
    · exact (Metric.isometry_inl x y).trans (hX x y)
    · exact MX.dist_le x y
  · intro x y
    apply realMetricRounded_dist_of_integer D hD
      (Sum.inr x : X ⊕ Y) (Sum.inr y) (MY.dist x y)
    · exact (Metric.isometry_inr x y).trans (hY x y)
    · exact MY.dist_le x y
  · intro x y h
    cases h

end IntegerMetric
end AllThoseEPPA
