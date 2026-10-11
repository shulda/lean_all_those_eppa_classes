import AllThoseEPPA.Examples.IntegerMetricBridge
import AllThoseEPPA.Examples.IntegerMetricShortestPaths

/-!
# Canonical symmetric costs of partially distance-coloured structures

This is the actual input-to-completion bridge for the metric EPPA
regression. An arbitrary finite relational witness need not itself
be a complete metric, and its relations cannot be treated as a
distance matrix before the following three consistency conditions:

* no loops carrying positive distance colours;
* every realised colour occurs in both orientations;
* a pair cannot carry two different distance colours.

Once these conditions hold and D>0, assign the unique labelled
length to each existing edge and the default length D to every
unlabelled pair of distinct vertices. This defines symmetric
strictly-positive D-bounded costs on exactly the original carrier,
without making any noncanonical choice of a colour or orientation.

The shortest-path completion of these costs is the intended
automorphism-equivariant metric completion of locally consistent
partial colour structures. Its preservation of the old edges
under small ordinary metric completions is the next theorem.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Three basic shape constraints for the relational language of
integer metrics: positive colours are loop-free, symmetric and
pairwise unique. None of the full metric triangle inequalities
is required at this point. -/
structure IsConsistentPartialMetric
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V) : Prop where
  no_loops :
    ∀ (d : Fin D) (x : V),
      ¬ B.rel (RelSymbol.edge d) ![x, x]
  symmetric :
    ∀ (d : Fin D) (x y : V),
      B.rel (RelSymbol.edge d) ![x, y] →
        B.rel (RelSymbol.edge d) ![y, x]
  unique :
    ∀ (d e : Fin D) (x y : V),
      B.rel (RelSymbol.edge d) ![x, y] →
      B.rel (RelSymbol.edge e) ![x, y] →
        d = e

/-- Direct candidate cost: zero on the diagonal; the
prescribed positive distance on an already coloured pair;
and D on any as yet uncoloured pair. Choice of a colour is
unambiguous under IsConsistentPartialMetric.unique. -/
noncomputable def candidateCost
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V) (x y : V) : ℕ := by
  classical
  exact if x = y then 0 else
    if h : ∃ d : Fin D, B.rel (RelSymbol.edge d) ![x, y] then
      (Classical.choose h).val + 1
    else D

/-- A labelled pair receives exactly its specified length.
This depends on uniqueness of the label, not on any metric
triangle inequality. -/
theorem candidateCost_of_edge
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (d : Fin D) {x y : V}
    (hd : B.rel (RelSymbol.edge d) ![x, y]) :
    candidateCost B x y = d.val + 1 := by
  classical
  have hxy : x ≠ y := by
    intro heq
    subst y
    exact hB.no_loops d x hd
  have hExists :
      ∃ e : Fin D, B.rel (RelSymbol.edge e) ![x, y] :=
    ⟨d, hd⟩
  have hChosen : Classical.choose hExists = d :=
    hB.unique (Classical.choose hExists) d x y
      (Classical.choose_spec hExists) hd
  simp [candidateCost, hxy, hExists, hChosen]

/-- A distinct pair without any distance colour receives the
default cost D. -/
theorem candidateCost_of_no_edge
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    {x y : V} (hxy : x ≠ y)
    (hAbsent :
      ¬ ∃ d : Fin D, B.rel (RelSymbol.edge d) ![x, y]) :
    candidateCost B x y = D := by
  classical
  simp [candidateCost, hxy, hAbsent]

/-- Complete all uncoloured pairs by D to obtain a symmetric
cost matrix. Its shortest-path completion will satisfy the
metric triangle inequality. D>0 is essential for strict
positivity of the default cost; D=0 is handled separately
by the already formalized EPPA base case. -/
noncomputable def toSymmetricCost
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D) : SymmetricCost D V := by
  classical
  refine {
    cost := candidateCost B
    cost_self := ?_
    cost_pos := ?_
    cost_symm := ?_
    cost_le := ?_ }
  · intro x
    simp [candidateCost]
  · intro x y hxy
    by_cases hExists :
        ∃ d : Fin D, B.rel (RelSymbol.edge d) ![x, y]
    · have hp : 0 < (Classical.choose hExists).val + 1 :=
        Nat.succ_pos _
      simpa [candidateCost, hxy, hExists] using hp
    · simpa [candidateCost, hxy, hExists] using hD
  · intro x y
    by_cases hxy : x = y
    · subst y
      rfl
    · by_cases hExists :
          ∃ d : Fin D, B.rel (RelSymbol.edge d) ![x, y]
      · obtain ⟨d, hd⟩ := hExists
        rw [candidateCost_of_edge B hB d hd,
            candidateCost_of_edge B hB d
              (hB.symmetric d x y hd)]
      · have hReverse :
            ¬ ∃ d : Fin D,
              B.rel (RelSymbol.edge d) ![y, x] := by
          rintro ⟨d, hd⟩
          exact hExists ⟨d, hB.symmetric d y x hd⟩
        rw [candidateCost_of_no_edge B hxy hExists,
            candidateCost_of_no_edge B hxy.symm hReverse]
  · intro x y
    by_cases hxy : x = y
    · subst y
      simp [candidateCost]
    · by_cases hExists :
          ∃ d : Fin D, B.rel (RelSymbol.edge d) ![x, y]
      · have hlt := (Classical.choose hExists).isLt
        have hle : (Classical.choose hExists).val + 1 ≤ D :=
          Nat.succ_le_of_lt hlt
        simpa [candidateCost, hxy, hExists] using hle
      · simp [candidateCost, hxy, hExists]

/-- The canonical symmetric costs preserve every existing
edge length exactly. -/
theorem toSymmetricCost_edge
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D)
    (d : Fin D) {x y : V}
    (hd : B.rel (RelSymbol.edge d) ![x, y]) :
    (toSymmetricCost B hB hD).cost x y = d.val + 1 :=
  candidateCost_of_edge B hB d hd

end Bridge
end IntegerMetric
end AllThoseEPPA
