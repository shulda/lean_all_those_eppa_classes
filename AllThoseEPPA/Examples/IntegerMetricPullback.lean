import AllThoseEPPA.Examples.IntegerMetricBasic

/-!
# Pull back an integer metric along an injective map

An abstract amalgamation interface permits the common source to be
an arbitrary relational structure Q. If Q embeds exactly into a
complete D-metric encoding, its underlying point set inherits an
ordinary D-bounded metric by restriction.

This standalone elementary construction needs no finite carrier,
no positivity assumption on D, no choice of basepoints, and no
language action.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u v

/-- Every injective map into a bounded integer metric space
induces a genuine bounded integer metric on its source, for
all D (including zero and empty types). -/
def BoundedNatMetric.pullback
    {D : ℕ} {I : Type u} {V : Type v}
    (M : BoundedNatMetric D V)
    (f : I → V) (hf : Function.Injective f) :
    BoundedNatMetric D I where
  dist := fun x y => M.dist (f x) (f y)
  dist_self := by
    intro x
    exact M.dist_self (f x)
  eq_of_dist_eq_zero := by
    intro x y h
    exact hf (M.eq_of_dist_eq_zero h)
  dist_symm := by
    intro x y
    exact M.dist_symm (f x) (f y)
  dist_triangle := by
    intro x y z
    exact M.dist_triangle (f x) (f y) (f z)
  dist_le := by
    intro x y
    exact M.dist_le (f x) (f y)

/-- The pullback preserves all distances along its defining map
on the nose, rather than up to an approximation. -/
theorem BoundedNatMetric.pullback_dist
    {D : ℕ} {I : Type u} {V : Type v}
    (M : BoundedNatMetric D V)
    (f : I → V) (hf : Function.Injective f)
    (x y : I) :
    (M.pullback f hf).dist x y = M.dist (f x) (f y) :=
  rfl

end IntegerMetric
end AllThoseEPPA
