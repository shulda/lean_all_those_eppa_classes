import Mathlib.Tactic

/-!
# Integer metrics and diameter truncation

Foundational vocabulary for the next regression target:
EPPA for finite metric spaces whose distances lie in `{0,1,...,D}`,
uniformly in `D : ℕ`.

We represent integer-valued metrics by natural-number distance
functions and explicitly require that distinct points have positive
distance. The bounded version requires all distances to be at most D.

The cap operation `min D` preserves the triangle inequality.
This elementary fact is needed for shortest-path completions and
metric amalgamation with bounded diameter.

No EPPA assertion is made in this file.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

/-- A metric with distances in the nonnegative integers. -/
structure NatMetric (V : Type u) where
  dist : V → V → ℕ
  dist_self : ∀ x, dist x x = 0
  eq_of_dist_eq_zero : ∀ {x y}, dist x y = 0 → x = y
  dist_symm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

/-- An integer metric of diameter at most D, including D = 0. -/
structure BoundedNatMetric (D : ℕ) (V : Type u) extends NatMetric V where
  dist_le : ∀ x y, dist x y ≤ D

/-- Truncate a nonnegative integer to the range from 0 to D. -/
def cap (D a : ℕ) : ℕ := min D a

@[simp] theorem cap_zero (D : ℕ) : cap D 0 = 0 := by
  simp [cap]

theorem cap_le (D a : ℕ) : cap D a ≤ D := by
  simp [cap]

theorem cap_mono (D : ℕ) {a b : ℕ} (hab : a ≤ b) :
    cap D a ≤ cap D b := by
  unfold cap
  omega

/-- Truncation is subadditive, the key inequality for the
triangle inequality of a bounded shortest-path metric. -/
theorem cap_add_le (D a b : ℕ) :
    cap D (a + b) ≤ cap D a + cap D b := by
  unfold cap
  omega

/-- Under the diameter bound, truncation leaves a length unchanged. -/
theorem cap_eq_of_le (D a : ℕ) (ha : a ≤ D) : cap D a = a := by
  unfold cap
  omega

namespace NatMetric

/-- Different points have strictly positive distance. -/
theorem dist_pos {V : Type u} (M : NatMetric V)
    {x y : V} (hxy : x ≠ y) : 0 < M.dist x y := by
  by_contra h
  have hzero : M.dist x y = 0 := by omega
  exact hxy (M.eq_of_dist_eq_zero hzero)

/-- Diameter truncation is again a genuine metric when D is positive.
The case D = 0 is separately handled by `BoundedNatMetric.subsingleton_of_zero`. -/
def truncate {V : Type u} (M : NatMetric V)
    (D : ℕ) (hD : 0 < D) : BoundedNatMetric D V where
  dist := fun x y => cap D (M.dist x y)
  dist_self := by
    intro x
    simp [cap, M.dist_self]
  eq_of_dist_eq_zero := by
    intro x y h
    apply M.eq_of_dist_eq_zero
    change cap D (M.dist x y) = 0 at h
    unfold cap at h
    omega
  dist_symm := by
    intro x y
    simp only [M.dist_symm]
  dist_triangle := by
    intro x y z
    exact (cap_mono D (M.dist_triangle x y z)).trans
      (cap_add_le D (M.dist x y) (M.dist y z))
  dist_le := by
    intro x y
    exact cap_le D (M.dist x y)

/-- A distance already at most D is unaffected by truncation. -/
theorem truncate_dist_of_le {V : Type u} (M : NatMetric V)
    (D : ℕ) (hD : 0 < D) (x y : V)
    (h : M.dist x y ≤ D) :
    (M.truncate D hD).dist x y = M.dist x y := by
  exact cap_eq_of_le D (M.dist x y) h

end NatMetric

namespace BoundedNatMetric

/-- A zero-diameter integer metric has at most one point. -/
theorem subsingleton_of_zero {V : Type u}
    (M : BoundedNatMetric 0 V) : Subsingleton V := by
  refine ⟨?_⟩
  intro x y
  apply M.eq_of_dist_eq_zero
  have h := M.dist_le x y
  omega

/-- Forgetting the upper bound recovers an integer metric. -/
def forgetBound {D : ℕ} {V : Type u}
    (M : BoundedNatMetric D V) : NatMetric V := M.toNatMetric

/-- A bounded metric is unchanged by the canonical truncation. -/
theorem truncate_forgetBound_dist {D : ℕ} {V : Type u}
    (M : BoundedNatMetric D V) (hD : 0 < D) (x y : V) :
    ((M.forgetBound).truncate D hD).dist x y = M.dist x y :=
  cap_eq_of_le D (M.dist x y) (M.dist_le x y)

end BoundedNatMetric
end IntegerMetric
end AllThoseEPPA
