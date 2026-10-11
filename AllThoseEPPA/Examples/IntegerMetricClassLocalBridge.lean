import AllThoseEPPA.Examples.IntegerMetricSmallPairCompletions
import AllThoseEPPA.StrongCompletionSmallTrees

/-!
# Exact metric semantics of the manuscript's small K-completion premise

Definition 11.2 in the formalized paper assumes only ORDINARY
homomorphism-embedding completions of all small closed pieces
into some finite member of an amalgamation class K.

For the class of complete D-bounded metric encodings, any such
completion is automatically one of our actual metric completions.
The quantitative bound n is unchanged, and no injectivity of
the small homomorphism-embedding is assumed or introduced.

This is the formal handoff from the paper's locally finite class
API to the metric-shortcut/local-certificate theorems.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Metric-class completion data for an arbitrary finite
amalgamation class K. We require only the semantic identification
of K-members as genuine bounded metrics, not any EPPA property. -/
theorem smallClassCompletions_imply_smallMetricCompletions
    {D : ℕ} {V : Type u} [Finite V]
    (B : Structure (language D) V)
    (n : ℕ)
    (K : TreeLike.FiniteAmalgamationClass (action D))
    (hMetric :
      ∀ {W : Type u} (C : Structure (language D) W),
        K.mem C → ∃ (M : BoundedNatMetric D W),
          C = toStructure M)
    (hSmall :
      ∀ (S : Set V) (hS : B.IsClosed S),
        S.ncard ≤ n →
          K.HasCompletion (B.induce S hS)) :
    HasSmallMetricHomEmbCompletions B n := by
  intro S hCard
  have hClosed : B.IsClosed S := allSubsetsClosed B S
  obtain ⟨W, hW, C, hC, f, hf⟩ :=
    hSmall S hClosed hCard
  obtain ⟨M, hEq⟩ := hMetric C hC
  subst C
  exact ⟨W, M, f, hf⟩

end Bridge
end IntegerMetric
end AllThoseEPPA
