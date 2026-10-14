import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportsReachable
import AllThoseEPPA.Applications.KOrientations.ReconstructionDConditional

/-!
# Rooted d-class membership of the reconstructed orientation

The two complementary root-support inclusions are now assembled:

1. Monotonicity of canonical supports along directed paths gives
   roots_B(u) ⊆ support(u).
2. Common support localization, exact source-copy reconstruction,
   lifting source paths, and inverse automorphism transport give
   support(u) ⊆ roots_B(u).

The resulting theorem packages a finite k-orientation with nonempty
root sets and the exact d-language expansion obtained from the
reconstructed directed graph. No statement of EPPA faithfulness or
coherence is asserted here; those are subsequent gluing obligations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The reconstructed graph has nonempty root sets, and their exact
values are precisely the tagged canonical intrinsic supports. -/
theorem faithful_reconstructed_exact_roots_and_rooted
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    (faithfulReconstructedDigraph G k S B ι hFaith).HasReachableRoots k ∧
      (∀ z : ReconstructedCarrier G k B,
        (faithfulReconstructedDigraph G k S B ι hFaith).roots k z =
        (Sum.inl : W → ReconstructedCarrier G k B) ''
          reconstructedSupport G k B z) := by
  apply faithful_reconstructed_rooted_and_exact_support
    G k S hBound hClosed hRooted B ι hFaith
  exact faithful_reconstructed_support_reachable
    G k S hClosed hRooted B ι hFaith

/-- The complete rooted k-orientation, together with its canonical
d-structure, is now constructed from B₀ and B₁. -/
theorem faithful_reconstructed_exists_rooted_k_orientation
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    ∃ K : KOrientation (ReconstructedCarrier G k B) k,
      K.graph.HasReachableRoots k ∧
      (∀ z : ReconstructedCarrier G k B,
        K.graph.roots k z =
          (Sum.inl : W → ReconstructedCarrier G k B) ''
            reconstructedSupport G k B z) ∧
      dStructure K.graph k =
        faithful_reconstructed_dStructure G k S B ι hFaith := by
  refine ⟨faithfulReconstructedKOrientation
    G k S hBound B ι hFaith, ?_, ?_, rfl⟩
  · exact (faithful_reconstructed_exact_roots_and_rooted
      G k S hBound hClosed hRooted B ι hFaith).1
  · exact (faithful_reconstructed_exact_roots_and_rooted
      G k S hBound hClosed hRooted B ι hFaith).2

end AllThoseEPPA.Applications.KOrientations
