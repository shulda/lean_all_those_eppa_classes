import AllThoseEPPA.Examples.IntegerMetricCanonicalAutomorphismLift
import AllThoseEPPA.Examples.IntegerMetricIrreducible
import AllThoseEPPA.AutomorphismPreservingCompletion

/-!
# Canonical metric completion satisfies the manuscript's exact AP-strong API

The previous modules have independently checked or isolated:

* Shortest-path completion is an actual bounded integer metric.
* Small metric completions preserve all original positive edge labels.
* Old irreducible substructures contain all pairs and hence receive
  no new relations in the canonical completion.
* The identity point-map gives an injective homomorphism-embedding.
* Every automorphism of the partial source preserves the canonical
  completed metric, with an identity- and composition-preserving lift.

This file packages these clauses in the exact structure
Structure.AutomorphismPreservingStrongCompletion used in the
general locally finite EPPA transfer theorem. The result has no
assumption that the original partial structure is complete or
already a metric.

The still missing class-wide local finiteness input is separate:
the small completions have to be obtained by amalgamation.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Given exact preservation of the original distance labels,
canonical shortest-path metric completion is an injective
automorphism-preserving strong completion in the paper's API. -/
noncomputable def canonicalAutomorphismPreservingStrongCompletion
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D)
    (hOld : ∀ (d : Fin D) (x y : V),
      B.rel (RelSymbol.edge d) ![x,y] →
        (toSymmetricCost B hB hD).completedMetric.dist x y =
          d.val + 1) :
    Structure.AutomorphismPreservingStrongCompletion
      (action D) B
      (toStructure (toSymmetricCost B hB hD).completedMetric) where
  irreducible_target :=
    metricEncoding_isIrreducible
      (toSymmetricCost B hB hD).completedMetric
  toHomomorphism :=
    canonicalCompletionHom B hB hD hOld
  injective := by
    intro x y h
    exact h
  homomorphismEmbedding :=
    canonicalCompletionHom_isHomomorphismEmbedding B hB hD hOld
  lift := liftAutomorphismToCanonicalCompletion B hB hD
  lift_lang := by
    intro g
    change
      (liftAutomorphismToCanonicalCompletion B hB hD g).lang * 1 =
        1 * g.lang
    rw [liftAutomorphismToCanonicalCompletion_lang]
    simp
  lift_apply := by
    intro g x
    exact liftAutomorphismToCanonicalCompletion_apply B hB hD g x
  lift_id :=
    liftAutomorphismToCanonicalCompletion_id B hB hD
  lift_comp := by
    intro g f
    exact liftAutomorphismToCanonicalCompletion_comp B hB hD g f

/-- If every induced substructure of size at most
max D 2 has an ordinary homomorphism-embedding completion
in a genuine D-bounded integer metric, then the FULL
automorphism-preserving strong completion exists on the
same finite carrier as B. This is the exact local finiteness
conclusion needed in the paper, not a proxy distance matrix. -/
theorem hasCanonicalAutomorphismPreservingStrongCompletion_of_smallCompletions
    {D : ℕ} {V : Type u} [Finite V]
    (B : Structure (language D) V)
    (hD : 0 < D)
    (hSmall : HasSmallMetricHomEmbCompletions B (max D 2)) :
    ∃ (hB : IsConsistentPartialMetric B),
      Nonempty (Structure.AutomorphismPreservingStrongCompletion
        (action D) B
        (toStructure (toSymmetricCost B hB hD).completedMetric)) := by
  obtain ⟨hB, hOld⟩ :=
    canonicalCompletion_preserves_oldEdges_of_smallMetricCompletions
      B hD hSmall
  exact ⟨hB,
    ⟨canonicalAutomorphismPreservingStrongCompletion B hB hD hOld⟩⟩

end Bridge
end IntegerMetric
end AllThoseEPPA
