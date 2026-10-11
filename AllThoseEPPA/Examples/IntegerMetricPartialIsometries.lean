import AllThoseEPPA.Examples.IntegerMetricBridge
import AllThoseEPPA.PartialIso

/-!
# Partial metric isometries are partial automorphisms of the encoding

The final standalone metric EPPA theorem speaks about an arbitrary
isometry p:U≃T between two subsets of the finite original metric A.
The verified general EPPA construction instead extends partial
Γ-automorphisms of the relational encoding.

This file proves that every such partial isometry is exactly a
partial automorphism of the encoded metric structure, for all
D including D=0. There are no additional constraints on U or T:
the language has no functions, so ALL vertex subsets are closed.
The symbol action is trivial and no ordered choice is introduced.

The eventual reader-facing EPPA theorem must explicitly make
this conversion before invoking the checked IsEPPAWitness API.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- A bijection between arbitrary subsets as a partial equivalence
of the whole vertex type, with unchanged values on its source. -/
noncomputable def metricPartialEquiv
    {V : Type u} (U T : Set V) (p : U ≃ T) :
    PartialEquiv V V := by
  classical
  exact {
    toFun x := if hx : x ∈ U then (p ⟨x,hx⟩).1 else x
    invFun y := if hy : y ∈ T then (p.symm ⟨y,hy⟩).1 else y
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

@[simp] theorem metricPartialEquiv_apply_of_mem
    {V : Type u} {U T : Set V} (p : U ≃ T)
    {x : V} (hx : x ∈ U) :
    metricPartialEquiv U T p x = (p ⟨x,hx⟩).1 := by
  simp [metricPartialEquiv,hx]

/-- The partial automorphism of the complete distance-colour
encoding canonically induced by a genuine partial isometry
of the original D-metric. -/
noncomputable def partialAutomorphism_of_partialIsometry
    {D : ℕ} {V : Type u}
    (A : BoundedNatMetric D V)
    (U T : Set V) (p : U ≃ T)
    (hp : ∀ x y : U,
      A.dist x.1 y.1 = A.dist (p x).1 (p y).1) :
    Structure.PartialAutomorphism (action D) (toStructure A) where
  lang := 1
  toPartialEquiv := metricPartialEquiv U T p
  source_closed := by
    intro n F xs hxs y hy
    exact F.elim
  target_closed := by
    intro n F xs hxs y hy
    exact F.elim
  map_rel_iff := by
    intro n R xs hxs
    cases R with
    | edge d =>
      have hx0 : xs 0 ∈ U := hxs 0
      have hx1 : xs 1 ∈ U := hxs 1
      have hdist :=
        hp ⟨xs 0,hx0⟩ ⟨xs 1,hx1⟩
      simp only [action_on_edge]
      change
        A.dist ((metricPartialEquiv U T p ∘ xs) 0)
               ((metricPartialEquiv U T p ∘ xs) 1) =
            d.val + 1 ↔ A.dist (xs 0) (xs 1) = d.val + 1
      simp only [Function.comp_apply,
        metricPartialEquiv_apply_of_mem p hx0,
        metricPartialEquiv_apply_of_mem p hx1]
      rw [hdist]
  map_func := by
    intro n F xs hxs
    exact F.elim

end Bridge
end IntegerMetric
end AllThoseEPPA
