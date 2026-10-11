import AllThoseEPPA.Examples.IntegerMetricPartialCosts
import AllThoseEPPA.Examples.IntegerMetricNoShortcuts

/-!
# Shortest-path completion does not invent unit-distance edges

Positive INTEGER edge costs imply that a walk of total weight 1
must contain exactly one (nontrivial) step of cost 1. Thus the
canonical shortest-path metric has distance 1 between x,y
if and only if their ORIGINAL direct cost is 1.

For partially distance-coloured structures and D >= 2, all
uncoloured distinct pairs are assigned the default cost D > 1.
Consequently the completed metric has a unit-distance edge
exactly when the ORIGINAL relation structure already had an
edge carrying the distance-one colour (index 0 : Fin D).

This is one of the two important mathematical components of
the stronger user-requested EPPA regression: preserve the
largest clique of pairwise distance one. The other component
is irreducible-structure faithfulness, showing that the
sparsified relational witness has no larger old unit-edge
clique than the original input. The special case D=1 must
be handled separately, since assigning default cost D=1
to missing edges *does* introduce unit edges.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

namespace Walk

/-- A positive-integer weighted walk of total weight one
can only be a single edge of weight one; the original
direct cost between its endpoints is therefore one. -/
theorem directCost_eq_one_of_weight_eq_one
    {D : ℕ} {V : Type u}
    (C : SymmetricCost D V) {x y : V}
    (p : Walk V x y) (hWeight : p.weight C = 1) :
    C.cost x y = 1 := by
  cases p with
  | nil a =>
      simp [weight] at hWeight
  | @step a b z hab tail =>
      cases tail with
      | nil b =>
          simpa [weight] using hWeight
      | @step b c z hbc rest =>
          have habPos : 0 < C.cost a b := C.cost_pos hab
          have hbcPos : 0 < C.cost b c := C.cost_pos hbc
          change C.cost a b + (C.cost b c + rest.weight C) = 1 at hWeight
          omega

end Walk

namespace SymmetricCost

variable {D : ℕ} {V : Type u}

/-- No positive-integer shortest-path completion introduces
new unit edges: distance one holds exactly on direct
cost-one pairs, even on infinite carriers. -/
theorem shortest_eq_one_iff_cost_eq_one
    (C : SymmetricCost D V) (x y : V) :
    C.shortest x y = 1 ↔ C.cost x y = 1 := by
  constructor
  · intro hShortest
    obtain ⟨p, hp⟩ := C.exists_shortest_walk x y
    exact p.directCost_eq_one_of_weight_eq_one C (hp.trans hShortest)
  · intro hCost
    by_cases hxy : x = y
    · subst y
      rw [C.cost_self] at hCost
      omega
    · have hPos := C.shortest_pos hxy
      have hBound := C.shortest_le_cost x y
      omega

end SymmetricCost

namespace Bridge

/-- In a consistent partially coloured structure with D >= 2,
every unit-cost pair must already carry a positive distance
relation of length precisely one. The case D=1 would be
false because the default unlabelled-edge cost is D=1. -/
theorem original_unit_edge_of_candidateCost_eq_one
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 1 < D)
    {x y : V}
    (hCost : candidateCost B x y = 1) :
    ∃ d : Fin D,
      B.rel (RelSymbol.edge d) ![x, y] ∧ d.val = 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [candidateCost] at hCost
  · by_cases hLabel :
        ∃ d : Fin D, B.rel (RelSymbol.edge d) ![x, y]
    · obtain ⟨d, hd⟩ := hLabel
      refine ⟨d, hd, ?_⟩
      have hValue := candidateCost_of_edge B hB d hd
      rw [hValue] at hCost
      omega
    · have hDefault := candidateCost_of_no_edge B hxy hLabel
      rw [hDefault] at hCost
      omega

/-- For D >= 2, unit-distance edges in the completed
metric are EXACTLY the original labelled distance-one
edges. No triangle inequalities on the partial source are
assumed (only consistency of old relation labels). -/
theorem completedMetric_unit_iff_old_unit
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 1 < D)
    (x y : V) :
    (toSymmetricCost B hB (by omega)).completedMetric.dist x y = 1 ↔
      ∃ d : Fin D,
        B.rel (RelSymbol.edge d) ![x, y] ∧ d.val = 0 := by
  let C : SymmetricCost D V :=
    toSymmetricCost B hB (by omega)
  change C.shortest x y = 1 ↔
    ∃ d : Fin D,
      B.rel (RelSymbol.edge d) ![x, y] ∧ d.val = 0
  rw [C.shortest_eq_one_iff_cost_eq_one]
  constructor
  · intro hOne
    exact original_unit_edge_of_candidateCost_eq_one
      B hB hD hOne
  · rintro ⟨d, hd, hd0⟩
    have hOld := candidateCost_of_edge B hB d hd
    change candidateCost B x y = 1
    rw [hOld, hd0]

end Bridge
end IntegerMetric
end AllThoseEPPA
