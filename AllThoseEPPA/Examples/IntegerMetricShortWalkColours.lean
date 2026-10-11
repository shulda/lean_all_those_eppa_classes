import AllThoseEPPA.Examples.IntegerMetricPartialCosts
import AllThoseEPPA.Examples.IntegerMetricWalkSupport

/-!
# Every shortcut in a partial metric is entirely on old labelled edges

The canonical candidate cost of an unlabelled distinct pair is D.
Hence no walk of total cost strictly less than D can traverse
an unlabelled edge. In particular, a walk which shortens an
existing direct distance d≤D is supported on at most D
vertices AND every nontrivial step is labelled in the
original relational structure.

This is the crucial reduction from path metric geometry to
the original relational homomorphism-embedding interface:
a local K-completion of the induced structure on these
at most D vertices preserves every step length needed for
the triangle-inequality contradiction.

The theorem works with genuine partial distance colours,
never assuming that every pair is already labelled.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

namespace Walk

/-- All nontrivial steps of this walk are realised by an
old binary distance-colour relation. -/
def AllEdgesColoured
    {D : ℕ} {V : Type u}
    (B : Structure (Bridge.language D) V)
    {x y : V} (p : Walk V x y) : Prop :=
  match p with
  | .nil _ => True
  | .step (x := a) (y := b) _ tail =>
      (∃ d : Fin D,
        B.rel (Bridge.RelSymbol.edge d) ![a, b]) ∧
        tail.AllEdgesColoured B

/-- Any walk shorter than D has all its nontrivial
steps explicitly labelled in the original structure:
an unlabelled step would already have cost D. -/
theorem allEdgesColoured_of_weight_lt_diameter
    {D : ℕ} {V : Type u}
    (B : Structure (Bridge.language D) V)
    (hB : Bridge.IsConsistentPartialMetric B)
    (hD : 0 < D)
    {x y : V} (p : Walk V x y)
    (hShort : p.weight (Bridge.toSymmetricCost B hB hD) < D) :
    p.AllEdgesColoured B := by
  revert hShort
  induction p with
  | nil a =>
      intro hShort
      trivial
  | @step a b z hab tail ih =>
      intro hShort
      have hSum :
          (Bridge.toSymmetricCost B hB hD).cost a b +
              tail.weight (Bridge.toSymmetricCost B hB hD) < D := by
        exact hShort
      have hEdgeShort :
          (Bridge.toSymmetricCost B hB hD).cost a b < D := by
        omega
      have hTailShort :
          tail.weight (Bridge.toSymmetricCost B hB hD) < D := by
        omega
      have hLabel :
          ∃ d : Fin D, B.rel (Bridge.RelSymbol.edge d) ![a, b] := by
        by_contra hMissing
        have hDefault :
            (Bridge.toSymmetricCost B hB hD).cost a b = D :=
          Bridge.candidateCost_of_no_edge B hab hMissing
        omega
      exact ⟨hLabel, ih hTailShort⟩

/-- Every shortcut of a prescribed candidate direct length
is not only supported on at most D vertices but uses only
edges that were already labelled in the source Γ-structure. -/
theorem shortcut_small_and_coloured
    {D : ℕ} {V : Type u} [DecidableEq V]
    (B : Structure (Bridge.language D) V)
    (hB : Bridge.IsConsistentPartialMetric B)
    (hD : 0 < D)
    {x y : V} (p : Walk V x y)
    (hShort :
      p.weight (Bridge.toSymmetricCost B hB hD) <
        (Bridge.toSymmetricCost B hB hD).cost x y) :
    p.support.card ≤ D ∧ p.AllEdgesColoured B := by
  have hSupport :=
    p.support_card_le_diameter_of_shortcut
      (Bridge.toSymmetricCost B hB hD) hShort
  have hWeight :
      p.weight (Bridge.toSymmetricCost B hB hD) < D :=
    hShort.trans_le
      ((Bridge.toSymmetricCost B hB hD).cost_le x y)
  exact ⟨hSupport,
    p.allEdgesColoured_of_weight_lt_diameter B hB hD hWeight⟩

end Walk
end IntegerMetric
end AllThoseEPPA
