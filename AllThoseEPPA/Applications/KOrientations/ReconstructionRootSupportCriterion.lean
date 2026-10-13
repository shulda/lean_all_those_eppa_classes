import AllThoseEPPA.Applications.KOrientations.ReconstructionRootSupportInclusion

/-!
# Exact root-support criterion for the reconstructed graph

The already checked support-antitonicity theorem proves one inclusion:
every path to a B₁-root endpoint stays inside the canonical support.

The reverse inclusion and exact root-sort identification are
separate, genuine mathematical obligations. This file isolates them:
if every B₁ vertex is a root, no canonical nonroot is a root, and
each element of support(u) is reachable in the reconstructed graph,
then the computed root set is exactly the tagged intrinsic support.

Keeping those hypotheses explicit prevents premature circular use
of membership in the d-closure class.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The two missing constructive obligations imply exactly the desired
identity of reconstructed reachable roots and intrinsic supports. -/
theorem faithful_reconstructed_roots_eq_taggedSupport_of_conditions
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (hRootSort : ∀ r : W,
      (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k (.inl r))
    (hNonrootSort : ∀ p : CanonicalNonroot G k B,
      ¬ (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k (.inr p))
    (hLift : ∀ (u : ReconstructedCarrier G k B) (r : W),
      r ∈ reconstructedSupport G k B u →
      (faithfulReconstructedDigraph G k S B ι hFaith).Reaches u (.inl r))
    (u : ReconstructedCarrier G k B) :
    (faithfulReconstructedDigraph G k S B ι hFaith).roots k u =
      (Sum.inl : W → ReconstructedCarrier G k B) ''
        reconstructedSupport G k B u := by
  ext z
  constructor
  · rintro ⟨hRoot, hReach⟩
    cases z with
    | inl r =>
        refine ⟨r, ?_, rfl⟩
        exact faithful_reconstructed_reachable_root_mem_support
          G k S B ι hFaith u r hReach
    | inr p =>
        exact (hNonrootSort p hRoot).elim
  · rintro ⟨r, hr, rfl⟩
    exact ⟨hRootSort r, hLift u r hr⟩

/-- The root-sort and path-lifting obligations also imply that
every reconstructed vertex reaches a root, since intrinsic supports
were already proved nonempty. -/
theorem faithful_reconstructed_hasReachableRoots_of_support_paths
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (hRootSort : ∀ r : W,
      (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k (.inl r))
    (hLift : ∀ (u : ReconstructedCarrier G k B) (r : W),
      r ∈ reconstructedSupport G k B u →
      (faithfulReconstructedDigraph G k S B ι hFaith).Reaches u (.inl r)) :
    (faithfulReconstructedDigraph G k S B ι hFaith).HasReachableRoots k := by
  intro u
  obtain ⟨r, hr⟩ := reconstructedSupport_nonempty G k B u
  exact ⟨Sum.inl r, hRootSort r, hLift u r hr⟩

end AllThoseEPPA.Applications.KOrientations
