import AllThoseEPPA.Examples.IntegerMetricBridge
import AllThoseEPPA.Irreducible
import Lean.Elab.Tactic.Omega

/-!
# Every complete finite integer metric encoding is irreducible

An important technical hypothesis of the manuscript's
restricted/tree-like EPPA theorem is that the input A is
irreducible. Unlike the partial intermediate EPPA witnesses,
the original integer-metric input is a complete edge-coloured
graph: every distinct pair has exactly one positive distance
colour. Therefore no nontrivial free decomposition can exist.

This verifies irreducibility for EVERY diameter parameter D,
including zero and empty/singleton inputs, rather than
silently treating metric irreducibility as an assumption.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- A purely binary relational structure in which every
distinct pair carries at least one distance-colour edge
is irreducible in the exact FreeDecomposition sense used
by the formalized EPPA paper. -/
theorem completeDistanceColoured_isIrreducible
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hComplete : ∀ x y : V, x ≠ y →
      ∃ d : Fin D, B.rel (RelSymbol.edge d) ![x,y]) :
    B.IsIrreducible := by
  constructor
  intro dec
  have hLeft : ∃ x : V, x ∉ dec.left := by
    by_contra h
    apply dec.left_proper
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hRight : ∃ y : V, y ∉ dec.right := by
    by_contra h
    apply dec.right_proper
    apply Set.eq_univ_of_forall
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hLeft
  obtain ⟨y, hy⟩ := hRight
  have hxy : x ≠ y := by
    intro he
    subst y
    have hBoth : x ∈ dec.left ∪ dec.right := by
      rw [dec.cover]
      exact Set.mem_univ x
    rcases hBoth with hl | hr
    · exact hx hl
    · exact hy hr
  obtain ⟨d, hd⟩ := hComplete x y hxy
  rcases dec.rel_local (RelSymbol.edge d) ![x,y] hd with hl | hr
  · exact hx (hl 0)
  · exact hy (hr 1)

/-- The relational encoding of any genuine integer metric
with distance alphabet {0,...,D} is irreducible in the exact
manuscript sense. No bound D>0 or nonempty-carrier hypothesis
is necessary. -/
theorem metricEncoding_isIrreducible
    {D : ℕ} {V : Type u}
    (M : BoundedNatMetric D V) :
    (toStructure M).IsIrreducible := by
  apply completeDistanceColoured_isIrreducible (toStructure M)
  intro x y hxy
  have hPos : 0 < M.dist x y :=
    M.toNatMetric.dist_pos hxy
  have hBound : M.dist x y ≤ D := M.dist_le x y
  let d : Fin D := ⟨M.dist x y - 1, by omega⟩
  refine ⟨d, ?_⟩
  change M.dist x y = d.val + 1
  change M.dist x y = M.dist x y - 1 + 1
  omega

end Bridge
end IntegerMetric
end AllThoseEPPA
