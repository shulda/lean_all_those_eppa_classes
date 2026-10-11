import AllThoseEPPA.Examples.IntegerMetricBasic

/-!
# Human-readable EPPA claim for finite bounded integer metrics

This file is deliberately a mathematical *contract*, independent of
the internal EPPA, Γ-language, homomorphism-embedding and locally finite
completion APIs. Its quantified statement only mentions:

* two finite sets of points;
* a metric on each, taking values in 0,...,D;
* an isometric injective copy of the old points;
* a partial isometry between arbitrary subsets of the old points;
* its extension to an isometry of the whole finite witness.

The corresponding theorem for ALL D is **not proved here yet**.
The sole proved regression in this file is the degenerate case D=0.
The ultimate all-D theorem must be derived from the checked general
EPPA machinery, so that it genuinely tests the formalized manuscript
and is not merely an unrelated proof of metric EPPA.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

/-- **Ordinary EPPA for finite metrics of diameter at most D.**

Every finite metric space A with integer distances 0,...,D
isometrically embeds in a finite metric space B using the same
allowed distances, and every isometry between *any two subsets*
of A extends to a global isometry of B.

The conclusion intentionally contains no reference to the
project's internal notion of EPPA or to Γ-homomorphism-embeddings.
The exact implication is what the final main-theorem regression
must establish. -/
def FiniteBoundedMetricsHaveEPPA (D : ℕ) : Prop :=
  ∀ {AType : Type u} [Finite AType]
    (A : BoundedNatMetric D AType),
    ∃ (BType : Type u) (_ : Finite BType)
      (B : BoundedNatMetric D BType)
      (ι : AType ↪ BType),

      -- The original A appears isometrically inside B.
      (∀ x y : AType, B.dist (ι x) (ι y) = A.dist x y) ∧

      -- Every partial isometry of A extends to an isometry of B.
      (∀ (U V : Set AType) (p : U ≃ V),
        (∀ x y : U,
          A.dist x.1 y.1 = A.dist (p x).1 (p y).1) →
        ∃ g : Equiv.Perm BType,
          (∀ x y : BType,
            B.dist (g x) (g y) = B.dist x y) ∧
          (∀ x : U, g (ι x.1) = ι (p x).1))

/-- The full regression goal, stated uniformly in the diameter
parameter. This proposition is currently an OPEN proof target,
not a theorem, assumption, or axiom. -/
def AllFiniteBoundedMetricsHaveEPPA : Prop :=
  ∀ D : ℕ, FiniteBoundedMetricsHaveEPPA.{u} D

/-- The human-readable metric regression is already verified
for diameter D=0: any such genuine metric has at most one point. -/
theorem finiteBoundedMetricsHaveEPPA_zero :
    FiniteBoundedMetricsHaveEPPA.{u} 0 := by
  intro AType hFinite A
  exact BoundedNatMetric.zero_diameter_eppa A

end IntegerMetric
end AllThoseEPPA
