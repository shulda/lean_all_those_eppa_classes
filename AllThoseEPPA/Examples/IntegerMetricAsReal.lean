import AllThoseEPPA.Examples.IntegerMetricBasic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Real metric-space presentation of a bounded natural metric

To use Mathlib's geometric metric gluing construction for finite
bounded integer metrics, each Nat-valued distance function must be
converted to a genuine MetricSpace whose real distance is exactly
the nat-cast of the original distance.

This file is the input bridge. Converting to reals does not lose
any distances or make new choices of metric geometry. The
follow-up uses Metric.GlueSpace and ceiling-and-diameter truncation
to transport finite strong metric amalgams back to integer metrics.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

/-- The usual real metric corresponding exactly to a natural-valued
metric; no finiteness or bound positivity is required. -/
noncomputable def NatMetric.toRealMetricSpace
    {V : Type u} (M : NatMetric V) : MetricSpace V where
  dist := fun x y => (M.dist x y : ℝ)
  dist_self := by
    intro x
    exact_mod_cast M.dist_self x
  dist_comm := by
    intro x y
    exact_mod_cast M.dist_symm x y
  dist_triangle := by
    intro x y z
    exact_mod_cast M.dist_triangle x y z
  eq_of_dist_eq_zero := by
    intro x y h
    apply M.eq_of_dist_eq_zero
    exact_mod_cast h

/-- The metric-space distance is definitionally the nat cast
of the original metric distance. -/
theorem NatMetric.toRealMetricSpace_dist
    {V : Type u} (M : NatMetric V) (x y : V) :
    letI : MetricSpace V := M.toRealMetricSpace
    _root_.dist x y = (M.dist x y : ℝ) := by
  rfl

end IntegerMetric
end AllThoseEPPA
