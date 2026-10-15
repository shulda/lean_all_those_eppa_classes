import AllThoseEPPA.Applications.KOrientations.IrreduciblePieceMove
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportEquivariance

/-!
# Simultaneous transport of irreducible d-pieces into the source-supported piece

The common-move theorem supplies one genuine B₁ automorphism f
sending the full support of every vertex of an irreducible closed
reconstructed d-piece into the embedded original roots.

The canonical reconstructed vertex permutation induced by f transports
supports exactly. Therefore it moves *all vertices of the entire
irreducible piece* into the fixed source-supported d-piece over the
image of the embedded original roots.

This is the geometric content of irreducible-structure faithfulness.
Packaging the source piece as an explicit d-embedding and the
permutation as a public Structure.Automorphism is a separate API step.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every irreducible closed d-piece admits a single second-stage
automorphism whose reconstructed action moves it into the fixed
source-supported piece. -/
theorem faithful_reconstructed_irreducible_piece_maps_into_source
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (D : Set (ReconstructedCarrier G k B))
    (hD : (dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed D)
    (hIrr : ((dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).induce
      D hD).IsIrreducible) :
    ∃ f : Structure.Automorphism (auxiliaryAction G k) B,
      ∀ z : ReconstructedCarrier G k B, z ∈ D →
        (reconstructedVertexPerm G k B f z) ∈
          reconstructedSupportedPiece G k B (Set.range ι.toFun) := by
  obtain ⟨f, hf⟩ :=
    faithful_reconstructed_irreducible_piece_common_move
      G k S hBound hClosed hRooted B ι hFaith D hD hIrr
  refine ⟨f, ?_⟩
  intro z hz
  change reconstructedSupport G k B
      (reconstructedVertexPerm G k B f z) ⊆ Set.range ι.toFun
  rw [faithful_reconstructedSupport_map G k S B ι hFaith f z]
  intro w hw
  obtain ⟨a, ha, rfl⟩ := hw
  obtain ⟨t, ht⟩ := hf z hz a ha
  exact ⟨t, ht.symm⟩

end AllThoseEPPA.Applications.KOrientations
