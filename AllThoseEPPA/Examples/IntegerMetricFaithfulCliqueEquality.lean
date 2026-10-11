import AllThoseEPPA.Examples.IntegerMetricUnitEdges
import AllThoseEPPA.Examples.IntegerMetricFaithfulCliqueTransfer
import AllThoseEPPA.Examples.IntegerMetricCliqueNumber

/-!
# Clique-number preservation by faithful shortest-path completion

This is the requested **stronger** metric regression mechanism,
isolated from the as-yet-unfinished all-D metric EPPA
construction.

For any finite source metric A, any faithful relational
witness B over its distance-colour language, D >= 2,
and any consistent partial-colour structure B for which
canonical shortest-path completion preserves the old A-copy
isometrically, the resulting completed metric has exactly
the same MAXIMUM size of pairwise distance-one clique as A.

The upper bound is NONTRIVIAL and uses both of the checked
main-theorem ingredients:

* unit distances in the completed metric correspond exactly
  to old unit-colour relations (no new unit edges);
* a clique of one colour is irreducible; the faithful B
  automorphism moves the entire clique into embedded A with
  exactly the same cardinality.

The reverse inequality is automatic from the isometric
inclusion A -> completed B.

This theorem makes explicit the missing hypothesis that
the canonical completed metric preserves the old embedded
A-copy. It does **not** assume or prove the final EPPA
property of the completed metric; the restricted tree-like
construction plus local metric completion must still
supply that witness and its extension property.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Canonical metric completion of a faithful relational
witness for D>=2 preserves exactly the maximum unit-clique
size of the original metric, provided the distinguished
copy of A remains isometric.

This statement is stronger than asserting that one
preselected forbidden K_n remains absent: it preserves
the whole maximum clique size without a size bound
hardcoded in the formalization. -/
theorem faithfulShortestPath_preserves_maximumUnitCliqueSize
    {D : ℕ} {V W : Type u} [Finite V] [Finite W]
    (A : BoundedNatMetric D V)
    (B : Structure (language D) W)
    (ψ : Structure.Embedding (action D) (toStructure A) B)
    (hFaith :
      Structure.IsIrreducibleStructureFaithful (action D) ψ)
    (hConsistent : IsConsistentPartialMetric B)
    (hD : 1 < D)
    (hIso :
      ∀ x y : V,
        (toSymmetricCost B hConsistent (by omega)).completedMetric.dist
            (ψ x) (ψ y) = A.dist x y) :
    maximumUnitCliqueSize
        (toSymmetricCost B hConsistent (by omega)).completedMetric =
      maximumUnitCliqueSize A := by
  classical
  let hDpos : 0 < D := by omega
  let C : SymmetricCost D W :=
    toSymmetricCost B hConsistent hDpos
  let M : BoundedNatMetric D W := C.completedMetric
  let unit : Fin D := ⟨0, by omega⟩
  have hTransfer :
      ∀ S : Finset W, IsUnitDistanceClique M S →
        ∃ T : Finset V, IsUnitDistanceClique A T ∧ S.card ≤ T.card := by
    intro S hS
    have hOld :
        ∀ x ∈ (S : Set W), ∀ y ∈ (S : Set W), x ≠ y →
          B.rel (RelSymbol.edge unit) ![x, y] := by
      intro x hx y hy hxy
      have hOne : M.dist x y = 1 := hS x hx y hy hxy
      have hOldOne :
          ∃ d : Fin D,
            B.rel (RelSymbol.edge d) ![x, y] ∧ d.val = 0 :=
        (completedMetric_unit_iff_old_unit B hConsistent hD x y).mp hOne
      obtain ⟨d, hd, hzero⟩ := hOldOne
      have hEqual : d = unit := Fin.ext hzero
      rw [hEqual] at hd
      exact hd
    obtain ⟨T, hCard, hCliqueOld⟩ :=
      faithful_monochromaticClique_preserves_cardinality
        (toStructure A) B ψ hFaith unit (S : Set W) hOld
    letI : Fintype V := Fintype.ofFinite V
    let U : Finset V := T.toFinset
    have hUnitU : IsUnitDistanceClique A U := by
      intro x hx y hy hxy
      have hxT : x ∈ T := by simpa [U] using hx
      have hyT : y ∈ T := by simpa [U] using hy
      have hRel := hCliqueOld x hxT y hyT hxy
      change A.dist x y = unit.val + 1 at hRel
      simpa [unit] using hRel
    have hCardU : U.card = S.card := by
      simpa [U] using hCard
    exact ⟨U, hUnitU, by omega⟩
  have hUpper :
      maximumUnitCliqueSize M ≤ maximumUnitCliqueSize A :=
    maximumUnitCliqueSize_le_of_cliqueTransfer A M hTransfer
  let ι : V ↪ W := ⟨ψ.toFun, ψ.injective⟩
  have hIso' :
      ∀ x y : V, M.dist (ι x) (ι y) = A.dist x y :=
    hIso
  have hLower :
      maximumUnitCliqueSize A ≤ maximumUnitCliqueSize M :=
    maximumUnitCliqueSize_le_of_isometricEmbedding A M ι hIso'
  exact Nat.le_antisymm hUpper hLower

end Bridge
end IntegerMetric
end AllThoseEPPA
