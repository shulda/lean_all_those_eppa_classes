import AllThoseEPPA.Applications.KOrientations.IrreduciblePieceSource
import AllThoseEPPA.Applications.KOrientations.FullDAutomorphism
import AllThoseEPPA.Applications.KOrientations.SupportedClosedPieces

/-!
# Irreducible-structure faithfulness of the reconstructed d-witness

The local faithful reconstruction has now produced all three parts:
1. a genuine rooted finite d-structure reconstructed from B₀ and B₁;
2. a canonical *closed source piece* whose vertices have full intrinsic
   B₁-support contained in the embedded original root sort;
3. for every irreducible closed d-piece D, a genuine B₁ automorphism
   moving all of D into the source piece simultaneously.

The induced second-stage vertex permutation is an actual total
d-automorphism in the public EPPA API. The inclusion of the canonical
source piece is a genuine Structure.Embedding. The following theorem
is therefore exactly `Structure.IsIrreducibleStructureFaithful` in
the public library, not a weaker geometric reformulation.

The **coherent extension property** remains a separate theorem.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The canonical source-supported piece, embedded by literal
inclusion into the full reconstructed d-structure. -/
noncomputable def faithful_reconstructed_sourcePieceEmbedding
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
    Structure.Embedding dTrivialAction
      ((dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).induce
        (reconstructedSupportedPiece G k B (Set.range ι.toFun))
        (faithful_reconstructed_supportedPiece_isClosed
          G k S hBound hClosed hRooted B ι hFaith
          (Set.range ι.toFun)))
      (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k) :=
  Structure.inclusion dTrivialAction
    (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k)
    (reconstructedSupportedPiece G k B (Set.range ι.toFun))
    (faithful_reconstructed_supportedPiece_isClosed
      G k S hBound hClosed hRooted B ι hFaith
      (Set.range ι.toFun))

/-- The second-stage construction yields an actual irreducible-
structure faithful d-witness for its canonical source piece. -/
theorem faithful_reconstructed_sourcePiece_irreducibleStructureFaithful
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
    Structure.IsIrreducibleStructureFaithful dTrivialAction
      (faithful_reconstructed_sourcePieceEmbedding
        G k S hBound hClosed hRooted B ι hFaith) := by
  intro D hD hIrr
  obtain ⟨f, hMap⟩ :=
    faithful_reconstructed_irreducible_piece_maps_into_source
      G k S hBound hClosed hRooted B ι hFaith D hD hIrr
  refine ⟨faithful_reconstructed_dAutomorphism_of_auxAutomorphism
    G k S B ι hFaith f, ?_⟩
  intro z hz
  refine ⟨⟨reconstructedVertexPerm G k B f z,
    hMap z hz⟩, ?_⟩
  exact faithful_reconstructed_dAutomorphism_apply
    G k S B ι hFaith f z

end AllThoseEPPA.Applications.KOrientations
