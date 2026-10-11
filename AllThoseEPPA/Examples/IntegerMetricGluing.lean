import AllThoseEPPA.Examples.IntegerMetricRealRounding
import Mathlib.Topology.MetricSpace.Gluing

/-!
# Finite bounded natural amalgams from Mathlib's real metric gluing

A genuine real metric pushout with isometric injections can be
rounded upwards to integer distances and truncated to D. The
rounding preserves every original (already integer) distance,
so the two embeddings remain exactly isometric after rounding.
The gluing space is finite when both sides are finite, since it
is a quotient of their disjoint union.

This is an amalgamation theorem in the useful *metric* language.
It establishes agreement on a common, nonempty interface. It
deliberately does not assert strong intersection here (which is
unnecessary for ordinary amalgamation), nor does it handle the
empty common interface (which is separately easy using cross
distance D).
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u v w

/-- A metric-space pushout of two finite real presentations
of bounded integer metrics, along an arbitrary nonempty
isometrically shared subspace, has a finite bounded integer
metric that extends each source exactly. -/
theorem finiteAmalgam_viaRealGlue
    {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    [Finite X] [Finite Y] [Nonempty Z]
    (D : ℕ) (hD : 0 < D)
    (MX : BoundedNatMetric D X)
    (MY : BoundedNatMetric D Y)
    {Φ : Z → X} {Ψ : Z → Y}
    (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (hX : ∀ x y : X, dist x y = (MX.dist x y : ℝ))
    (hY : ∀ x y : Y, dist x y = (MY.dist x y : ℝ)) :
    ∃ (W : Type (max u v)) (_ : Finite W)
      (M : BoundedNatMetric D W)
      (ιX : X → W) (ιY : Y → W),
      (∀ x y : X, M.dist (ιX x) (ιX y) = MX.dist x y) ∧
      (∀ x y : Y, M.dist (ιY x) (ιY y) = MY.dist x y) ∧
      (∀ z : Z, ιX (Φ z) = ιY (Ψ z)) := by
  classical
  letI : Finite (X ⊕ Y) := inferInstance
  have hFin : Finite (Metric.GlueSpace hΦ hΨ) := by
    unfold Metric.GlueSpace
    infer_instance
  let M : BoundedNatMetric D (Metric.GlueSpace hΦ hΨ) :=
    realMetricRounded D hD
  refine ⟨Metric.GlueSpace hΦ hΨ, hFin, M,
    Metric.toGlueL hΦ hΨ, Metric.toGlueR hΦ hΨ, ?_, ?_, ?_⟩
  · intro x y
    apply realMetricRounded_dist_of_integer D hD
      (Metric.toGlueL hΦ hΨ x) (Metric.toGlueL hΦ hΨ y)
      (MX.dist x y)
    · exact (Metric.toGlueL_isometry hΦ hΨ x y).trans (hX x y)
    · exact MX.dist_le x y
  · intro x y
    apply realMetricRounded_dist_of_integer D hD
      (Metric.toGlueR hΦ hΨ x) (Metric.toGlueR hΦ hΨ y)
      (MY.dist x y)
    · exact (Metric.toGlueR_isometry hΦ hΨ x y).trans (hY x y)
    · exact MY.dist_le x y
  · intro z
    exact congrFun (Metric.toGlue_commute hΦ hΨ) z

end IntegerMetric
end AllThoseEPPA
