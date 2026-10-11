import AllThoseEPPA.Examples.IntegerMetricAmalgamationClass
import AllThoseEPPA.Examples.IntegerMetricRestrictedToReadable
import AllThoseEPPA.Examples.IntegerMetricClassLocalBridge
import AllThoseEPPA.Examples.IntegerMetricIrreducible
import AllThoseEPPA.UnrestrictedFaithfulEPPA
import AllThoseEPPA.TreeLikeUnrestrictedMaintree
import AllThoseEPPA.StrongCompletionSmallTrees

/-!
# Strengthened integer-metric EPPA reduced to finite metric amalgamation

This is the intended nontrivial regression of the verified general
EPPA machinery against an ordinary mathematician-readable assertion:

  Every finite metric A with distances 0,...,D has a finite
  D-metric EPPA witness with exactly the same maximal size of a
  pairwise distance-one clique.

The theorem below derives this full, reader-facing conclusion
for any D>=2 from precisely ONE outstanding external mathematical
lemma, stated as an ordinary finite metric amalgamation law.
It invokes the actual checked unrestricted faithful/coherent EPPA
theorem, the genuine restricted/tree-like construction with small
full-A trees, Observation 9.4 (tree completion in an amalgamation
class), bounded local metric completions, canonical shortest paths,
and faithful maximum unit-clique equality.

The existence of the metric amalgamation operation is not smuggled
in as an axiom: it is a named Prop-valued hypothesis, which the
Mathlib GlueSpace branches will discharge. No all-D unconditional
EPPA theorem is asserted at this stage.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Assuming only finite D-metric amalgamation, the full
strengthened EPPA conclusion follows from the formalized
general paper constructions for every fixed D >= 2.

The proof uses the genuinely unrestricted ambient faithful
EPPA theorem, then the restricted/tree-like EPPA construction,
the real amalgamation-class API, and the canonical metric
completion. This is not a separate direct proof of metric EPPA. -/
theorem unitCliquePreservingMetricEPPA_of_finiteMetricAmalgamation
    (D : ℕ) (hD : 1 < D)
    (hAmalgam : HasFiniteMetricAmalgamation.{u} D) :
    FiniteBoundedMetricsHaveEPPAAndPreserveUnitClique.{u} D := by
  intro V hFinite A
  classical
  letI : Fintype V := Fintype.ofFinite V
  let K : TreeLike.FiniteAmalgamationClass (action D) :=
    finiteMetricEncodingAmalgamationClass D hAmalgam
  have hKA : K.mem (toStructure A) :=
    finiteMetricEncodingAmalgamationClass_mem hAmalgam A
  obtain ⟨W₀, hFinite₀, B₀, ψ₀, hCoh₀, _hFaith₀⟩ :=
    Faithful.finiteOrbitUnaryStructuresHaveFaithfulCoherentEPPA
      (action D) (toStructure A) (finiteOrbit A)
  letI : Finite W₀ := hFinite₀
  obtain ⟨c₀⟩ := hCoh₀
  have hInitialEPPA :
      Structure.IsEPPAWitness (action D) ψ₀ :=
    c₀.isEPPAWitness (action D)
  obtain ⟨W, hFiniteW, B, ψ, hEPPA, hFaith, _hProjection,
      hSmallTrees, _hOptionalCoh⟩ :=
    TreeLike.restrictedEPPA_from_any_witness
      (action D) (toStructure A) B₀ ψ₀ hInitialEPPA (max D 2)
  letI : Finite W := hFiniteW
  have hIrr : (toStructure A).IsIrreducible :=
    metricEncoding_isIrreducible A
  have hSmallK :
      ∀ (S : Set W) (hS : B.IsClosed S),
        S.ncard ≤ max D 2 →
          K.HasCompletion (B.induce S hS) :=
    TreeLike.smallClosedTrees_haveCompletions
      (action D) (toStructure A) hIrr
      K hKA B (max D 2) hSmallTrees
  have hMetric :
      ∀ {U : Type u} (C : Structure (language D) U),
        K.mem C → ∃ (MU : BoundedNatMetric D U),
          C = toStructure MU := by
    intro U C hC
    exact finiteMetricEncodingAmalgamationClass_members_are_metrics
      hAmalgam C hC
  have hSmallMetric :
      HasSmallMetricHomEmbCompletions B (max D 2) :=
    smallClassCompletions_imply_smallMetricCompletions
      B (max D 2) K hMetric hSmallK
  obtain ⟨M, ι, hIso, hExtensions, hUnitClique⟩ :=
    readableMetricEPPA_of_faithful_locallyCompletable
      A B ψ hEPPA hFaith hD hSmallMetric
  exact ⟨W, hFiniteW, M, ι, hIso, hExtensions, hUnitClique⟩

end Bridge
end IntegerMetric
end AllThoseEPPA
