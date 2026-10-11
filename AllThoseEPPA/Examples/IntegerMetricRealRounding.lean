import AllThoseEPPA.Examples.IntegerMetricBasic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# From arbitrary real metrics to bounded integer metrics

This is the discretization bridge for an alternative route to
the metric strong amalgamation property. Mathlib already contains
Metric.GlueSpace, which exactly amalgamates real metric spaces
along an isometric common subspace.

The pointwise ceiling of a nonnegative real metric is a genuine
integer metric: ceiling is monotone and subadditive. Truncating
at any positive diameter D then gives a bounded integer metric.

Crucially, if an original distance was already an integer ≤ D,
both operations leave it EXACTLY unchanged. Thus the existing
real metric gluing theorem can potentially discharge metric SAP
without a new large path-contraction proof in the integer setting.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

/-- Ceiling-and-cap discretization of ANY real metric. The
output has values in 0,...,D. No finite-carrier hypothesis
is needed and no values of the original metric are assumed
to be integral. D=0 is excluded because a nontrivial metric
cannot take only the value zero. -/
noncomputable def realMetricRounded
    {V : Type u} [MetricSpace V]
    (D : ℕ) (hD : 0 < D) : BoundedNatMetric D V where
  dist := fun x y => cap D (Nat.ceil (dist x y))
  dist_self := by
    intro x
    simp [cap, dist_self]
  eq_of_dist_eq_zero := by
    intro x y h
    have hceil : Nat.ceil (dist x y) = 0 := by
      change min D (Nat.ceil (dist x y)) = 0 at h
      omega
    have hle : dist x y ≤ (0 : ℝ) := by
      have h := Nat.le_ceil (dist x y)
      rw [hceil] at h
      simpa using h
    have hnonneg : (0 : ℝ) ≤ dist x y := dist_nonneg
    exact dist_eq_zero.mp (le_antisymm hle hnonneg)
  dist_symm := by
    intro x y
    simp only [dist_comm]
  dist_triangle := by
    intro x y z
    have htriangle : dist x z ≤ dist x y + dist y z :=
      dist_triangle x y z
    have hceil :
        Nat.ceil (dist x z) ≤
          Nat.ceil (dist x y) + Nat.ceil (dist y z) :=
      (Nat.ceil_mono htriangle).trans
        (Nat.ceil_add_le (dist x y) (dist y z))
    exact (cap_mono D hceil).trans
      (cap_add_le D (Nat.ceil (dist x y)) (Nat.ceil (dist y z)))
  dist_le := by
    intro x y
    exact cap_le D (Nat.ceil (dist x y))

/-- Real-isometric copies of a bounded integer metric stay
exactly isometric after ceiling-and-cap discretization.
This statement can be applied directly to both canonical
isometries into Mathlib's Metric.GlueSpace. -/
theorem realMetricRounded_dist_of_integer
    {V : Type u} [MetricSpace V]
    (D : ℕ) (hD : 0 < D) (x y : V)
    (d : ℕ) (hDistance : dist x y = (d : ℝ))
    (hd : d ≤ D) :
    (realMetricRounded D hD).dist x y = d := by
  change cap D (Nat.ceil (dist x y)) = d
  rw [hDistance]
  simpa using (cap_eq_of_le D d hd)

end IntegerMetric
end AllThoseEPPA
