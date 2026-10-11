import AllThoseEPPA.Examples.IntegerMetricReaderFacingEPPA
import AllThoseEPPA.FiniteSet

/-!
# Strong readable metric EPPA regression for diameter one

For D=1 every genuine metric is discrete: distinct points
are all at distance 1. Thus every partial isometry is an
arbitrary partial bijection, and the ordinary finite-set
EPPA theorem extends it to a permutation of the SAME
carrier. Choosing B=A automatically preserves the largest
distance-one clique size, including the empty case.

This is deliberately a corollary of the already formalized
finite-set part of the paper's EPPA machinery, not an
independent replacement for it.

When D=1, the shortcut completion default cost D equals 1
and would fill every missing edge with length 1. Therefore
the no-new-unit-edge argument for D>=2 is not used here.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

/-- All nonzero distances in a 1-bounded genuine integer
metric equal 1. -/
theorem boundedOne_dist_of_ne
    {V : Type u} (M : BoundedNatMetric 1 V)
    {x y : V} (hxy : x ≠ y) : M.dist x y = 1 := by
  have hPos : 0 < M.dist x y := M.toNatMetric.dist_pos hxy
  have hBound : M.dist x y ≤ 1 := M.dist_le x y
  omega

/-- Every permutation of the points of a 1-bounded metric
is automatically an isometry. -/
theorem boundedOne_perm_isometry
    {V : Type u} (M : BoundedNatMetric 1 V)
    (g : Equiv.Perm V) (x y : V) :
    M.dist (g x) (g y) = M.dist x y := by
  by_cases hxy : x = y
  · subst y
    simp only [M.dist_self]
  · have hgy : g x ≠ g y := by
      intro heq
      exact hxy (g.injective heq)
    rw [boundedOne_dist_of_ne M hgy,
      boundedOne_dist_of_ne M hxy]

/-- Encode a partial bijection between two arbitrary subsets
as an ordinary partial permutation of the full point set,
using the project's already formalized PartialEquiv API. -/
private noncomputable def subsetPartialEquiv
    {V : Type u} (U T : Set V) (p : U ≃ T) :
    PartialEquiv V V := by
  classical
  exact {
    toFun x := if hx : x ∈ U then (p ⟨x, hx⟩).1 else x
    invFun y := if hy : y ∈ T then (p.symm ⟨y, hy⟩).1 else y
    source := U
    target := T
    map_source' := by
      intro x hx
      simp [hx]
    map_target' := by
      intro y hy
      simp [hy]
    left_inv' := by
      intro x hx
      simp [hx]
    right_inv' := by
      intro y hy
      simp [hy]
  }

@[simp] private theorem subsetPartialEquiv_apply_of_mem
    {V : Type u} {U T : Set V} (p : U ≃ T)
    {x : V} (hx : x ∈ U) :
    subsetPartialEquiv U T p x = (p ⟨x, hx⟩).1 := by
  simp [subsetPartialEquiv, hx]

/-- The **strengthened** reader-facing metric EPPA statement
for D=1. The witness is exactly A itself: finite-set EPPA
extends all partial bijections, every permutation is an
isometry, and the largest unit-distance clique is obviously
unchanged. -/
theorem finiteBoundedMetricsHaveEPPAAndPreserveUnitClique_one :
    FiniteBoundedMetricsHaveEPPAAndPreserveUnitClique.{u} 1 := by
  intro AType hFinite A
  classical
  letI : Fintype AType := Fintype.ofFinite AType
  let ι : AType ↪ AType := ⟨id, by intro a b h; exact h⟩
  refine ⟨AType, inferInstance, A, ι, ?_, ?_, ?_⟩
  · intro x y
    rfl
  · intro U T p _hPartialIsometry
    obtain ⟨extension, hExtension, _, _⟩ :=
      AllThoseEPPA.finiteSetsHaveCoherentEPPA AType
    let q : PartialEquiv AType AType :=
      subsetPartialEquiv U T p
    refine ⟨extension q, ?_, ?_⟩
    · exact boundedOne_perm_isometry A (extension q)
    · intro x
      have hx : x.1 ∈ q.source := x.2
      have h := hExtension q x.1 hx
      change extension q x.1 = (p x).1
      simpa [q, subsetPartialEquiv, x.2] using h
  · rfl

end IntegerMetric
end AllThoseEPPA
