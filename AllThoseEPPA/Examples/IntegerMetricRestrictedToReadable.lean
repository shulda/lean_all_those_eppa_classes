import AllThoseEPPA.Examples.IntegerMetricFaithfulCliqueEquality
import AllThoseEPPA.Examples.IntegerMetricLocalShortcuts
import AllThoseEPPA.Examples.IntegerMetricPartialIsometries
import AllThoseEPPA.Examples.IntegerMetricCanonicalAutomorphismLift
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Finish the reader-facing metric EPPA conclusion from a faithful restricted witness

All the difficult paper-facing construction is factored into explicit,
independent hypotheses on a finite, RELATIONAL intermediate B:

* B is an actual EPPA witness for the full D-metric encoding A;
* B is irreducible-structure faithful to the original A;
* every induced subset with at most max(D,2) points admits an
  ordinary homomorphism-embedding completion into a D-bounded metric.

Those hypotheses are the precise output of the verified restricted/tree-like
construction together with the metric amalgamation theorem (the latter is
the outstanding global construction, NOT assumed here as an axiom).

This file derives a fully reader-facing, strengthened EPPA conclusion:
finite genuine D-bounded metric completion, isometric old copy,
extension of every arbitrary partial isometry, and unchanged maximum
unit-distance clique size. No Γ language or partial automorphism
appears in the final conclusion of the theorem.

The argument preserves the witness carrier exactly and invokes the
verified faithfulness-clique equality theorem, rather than relying on
a possibly noncanonical class completion.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- For D >= 2, a finite faithful restricted EPPA witness with all
small ordinary metric completions has a canonical, finite, genuine
metric completion satisfying the FULL strengthened EPPA regression
for its original input A, including equality of maximum unit-clique
sizes. This proves the last semantic bridge, conditional only on the
actual restricted-witness hypotheses obtained by metric amalgamation. -/
theorem readableMetricEPPA_of_faithful_locallyCompletable
    {D : ℕ} {V W : Type u} [Finite V] [Finite W]
    (A : BoundedNatMetric D V)
    (B : Structure (language D) W)
    (ψ : Structure.Embedding (action D) (toStructure A) B)
    (hEPPA : Structure.IsEPPAWitness (action D) ψ)
    (hFaith : Structure.IsIrreducibleStructureFaithful (action D) ψ)
    (hD : 1 < D)
    (hSmall : HasSmallMetricHomEmbCompletions B (max D 2)) :
    ∃ (M : BoundedNatMetric D W)
      (ι : V ↪ W),
      (∀ x y : V, M.dist (ι x) (ι y) = A.dist x y) ∧
      (∀ (U T : Set V) (p : U ≃ T),
        (∀ x y : U,
          A.dist x.1 y.1 = A.dist (p x).1 (p y).1) →
        ∃ g : Equiv.Perm W,
          (∀ x y : W, M.dist (g x) (g y) = M.dist x y) ∧
          (∀ x : U, g (ι x.1) = ι (p x).1)) ∧
      maximumUnitCliqueSize M = maximumUnitCliqueSize A := by
  classical
  have hDpos : 0 < D := by omega
  obtain ⟨hB, hOld⟩ :=
    canonicalCompletion_preserves_oldEdges_of_smallMetricCompletions
      B hDpos hSmall
  let M : BoundedNatMetric D W :=
    (toSymmetricCost B hB hDpos).completedMetric
  let ι : V ↪ W := ⟨ψ.toFun, ψ.injective⟩
  have hIso : ∀ x y : V, M.dist (ι x) (ι y) = A.dist x y := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rw [M.dist_self, A.dist_self]
    · have hPos : 0 < A.dist x y :=
        A.toNatMetric.dist_pos hxy
      have hBound : A.dist x y ≤ D := A.dist_le x y
      let d : Fin D := ⟨A.dist x y - 1, by omega⟩
      have hSrc : (toStructure A).rel (RelSymbol.edge d) ![x, y] := by
        change A.dist x y = A.dist x y - 1 + 1
        omega
      have hDst : B.rel (RelSymbol.edge d) ![ψ x, ψ y] := by
        have h :=
          (ψ.map_rel_iff (RelSymbol.edge d) ![x,y]).mpr hSrc
        have ht :
            (ψ.toFun ∘ (![x,y] : Fin 2 → V)) =
              (![ψ x, ψ y] : Fin 2 → W) := by
          funext i
          fin_cases i <;> rfl
        simpa only [action_on_edge, ht] using h
      have hKeep := hOld d (ψ x) (ψ y) hDst
      change M.dist (ι x) (ι y) =
        A.dist x y - 1 + 1 at hKeep
      omega
  have hMetricExtension :
      ∀ (U T : Set V) (p : U ≃ T),
        (∀ x y : U,
          A.dist x.1 y.1 = A.dist (p x).1 (p y).1) →
        ∃ g : Equiv.Perm W,
          (∀ x y : W, M.dist (g x) (g y) = M.dist x y) ∧
          (∀ x : U, g (ι x.1) = ι (p x).1) := by
    intro U T p hp
    let pRel := partialAutomorphism_of_partialIsometry A U T p hp
    obtain ⟨g, hg⟩ := hEPPA pRel
    refine ⟨g.toEquiv, ?_, ?_⟩
    · intro x y
      exact completedMetric_automorphism_isometry B hB hDpos g x y
    · intro x
      have hSource : x.1 ∈ pRel.source := x.2
      have hCommute := hg.2 x.1 hSource
      change g (ψ x.1) = ψ (metricPartialEquiv U T p x.1) at hCommute
      rw [metricPartialEquiv_apply_of_mem p x.2] at hCommute
      exact hCommute
  have hClique : maximumUnitCliqueSize M =
      maximumUnitCliqueSize A :=
    faithfulShortestPath_preserves_maximumUnitCliqueSize
      A B ψ hFaith hB hD (by
        intro x y
        exact hIso x y)
  exact ⟨M, ι, hIso, hMetricExtension, hClique⟩

end Bridge
end IntegerMetric
end AllThoseEPPA
