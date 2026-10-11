import AllThoseEPPA.Examples.IntegerMetricBasic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

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

Two standalone EPPA propositions are recorded: ordinary EPPA and its
strengthening preserving the largest clique of mutual distance one.
Their unconditional proofs for ALL D appear in
`IntegerMetricAllDMainTheorem.lean`, under the names
`Bridge.allFiniteBoundedMetricsHaveEPPA` and
`Bridge.allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique`.
The latter genuinely uses the checked faithful restricted/tree-like
EPPA machinery from the formalized manuscript, rather than an external
metric EPPA theorem. The elementary D=0 proof is also given here.
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
This is proved by `Bridge.allFiniteBoundedMetricsHaveEPPA`
in `IntegerMetricAllDMainTheorem.lean`. -/
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

/-- A set of vertices is a distance-one clique when every
two *distinct* members have distance exactly 1. In particular
singletons and the empty set count as cliques. -/
def IsUnitDistanceClique {D : ℕ} {V : Type u}
    (M : BoundedNatMetric D V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → M.dist x y = 1

/-- The largest possible cardinality of a distance-one clique.
For an empty metric space it is 0; for a nonempty space with
D=0 it is 1. This is the ordinary finite clique number of
the graph whose edges connect pairs at distance exactly 1. -/
noncomputable def maximumUnitCliqueSize
    {D : ℕ} {V : Type u} [Finite V]
    (M : BoundedNatMetric D V) : ℕ := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact (Finset.univ.powerset).sup (fun S : Finset V =>
    if IsUnitDistanceClique M S then S.card else 0)

/-- **Stronger readable regression:** the ordinary finite
D-metric EPPA witness can be chosen without increasing the
largest distance-one clique. The old copy is isometric,
so equality of the two clique numbers is the natural
statement rather than merely an inequality.

This is the full user-requested test of the strength of
irreducible-structure faithfulness plus the checked
restricted / locally finite EPPA construction. -/
def FiniteBoundedMetricsHaveEPPAAndPreserveUnitClique
    (D : ℕ) : Prop :=
  ∀ {AType : Type u} [Finite AType]
    (A : BoundedNatMetric D AType),
    ∃ (BType : Type u) (_ : Finite BType)
      (B : BoundedNatMetric D BType)
      (ι : AType ↪ BType),
      (∀ x y : AType, B.dist (ι x) (ι y) = A.dist x y) ∧
      (∀ (U V : Set AType) (p : U ≃ V),
        (∀ x y : U,
          A.dist x.1 y.1 = A.dist (p x).1 (p y).1) →
        ∃ g : Equiv.Perm BType,
          (∀ x y : BType,
            B.dist (g x) (g y) = B.dist x y) ∧
          (∀ x : U, g (ι x.1) = ι (p x).1)) ∧
      maximumUnitCliqueSize B = maximumUnitCliqueSize A

/-- The strengthened all-D proposition (not an axiom).
The unconditional proof is
`Bridge.allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique`
in `IntegerMetricAllDMainTheorem.lean`. -/
def AllFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique : Prop :=
  ∀ D : ℕ, FiniteBoundedMetricsHaveEPPAAndPreserveUnitClique.{u} D

/-- Forgetting the clique requirement yields ordinary metric EPPA.
The strengthened statement is not a substitute for the old test;
it is a genuine refinement. -/
theorem unitCliquePreservingEPPA_implies_EPPA
    (D : ℕ)
    (h : FiniteBoundedMetricsHaveEPPAAndPreserveUnitClique.{u} D) :
    FiniteBoundedMetricsHaveEPPA.{u} D := by
  intro AType hFinite A
  obtain ⟨BType, hB, B, ι, hIso, hExtension, _⟩ := h A
  exact ⟨BType, hB, B, ι, hIso, hExtension⟩

/-- The strengthened test holds at D=0, with the identity
witness. It preserves the maximum distance-one clique,
including when the input space is empty. -/
theorem finiteBoundedMetricsHaveEPPAAndPreserveUnitClique_zero :
    FiniteBoundedMetricsHaveEPPAAndPreserveUnitClique.{u} 0 := by
  intro AType hFinite A
  letI : Subsingleton AType := A.subsingleton_of_zero
  let ι : AType ↪ AType := ⟨id, by intro a b h; exact h⟩
  refine ⟨AType, inferInstance, A, ι, ?_, ?_, ?_⟩
  · intro x y
    rfl
  · intro U V p _hPartialIsometry
    refine ⟨Equiv.refl AType, ?_, ?_⟩
    · intro x y
      rfl
    · intro x
      exact Subsingleton.elim _ _
  · rfl

/-- Ordinary metric EPPA for all diameter bounds. This named proposition
is proved unconditionally by `Bridge.allFiniteBoundedMetricsHaveEPPA`
in `IntegerMetricAllDMainTheorem.lean`; it is not an axiom. -/
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
