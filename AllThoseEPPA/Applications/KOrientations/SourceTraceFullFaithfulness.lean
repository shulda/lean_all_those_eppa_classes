import AllThoseEPPA.Applications.KOrientations.SourceSupportedDTraceIso
import AllThoseEPPA.Applications.KOrientations.ReconstructedSourceFaithfulness

/-!
# The original intrinsic d-trace embeds irreducible-structure faithfully into the FULL reconstruction

The canonical source-supported piece of the second-stage
reconstructed d-witness has two independently certified properties:
(1) it is bijectively d-isomorphic, with all actual set-valued
    F_n symbols, to the intrinsic original source d-trace;
(2) its inclusion in the full reconstructed d-structure is genuinely
    irreducible-structure faithful.

Compose the two checked Structure.Embedding objects to obtain an
explicit original-source-to-whole-witness embedding. Since the
first embedding is surjective onto the canonical supported piece,
the irreducible-structure faithfulness of its inclusion transfers
to the actual original-source embedding, not merely to a named
auxiliary induced substructure. This is the correct geometric
input for the last two-stage coherent EPPA gluing argument.
No assumption that the original source S is d-closed in the
ambient first witness is made.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Exact canonical embedding of the source's INTRINSIC d-trace
into the entire second-stage reconstructed d-structure,
preserving AND reflecting all oriented edges and full F_n
set-valued function fibres. -/
noncomputable def faithful_sourceFull_dTraceEmbedding
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
      (dTraceStructure G k S)
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k) :=
  (faithful_reconstructed_sourcePieceEmbedding
    G k S hBound hClosed hRooted B ι hFaith).comp
    (faithful_sourceSupported_dTraceEmbedding
      G k S hBound hClosed hRooted B ι hFaith)

/-- The actual original intrinsic d-trace is itself embedded
irreducible-structure faithfully into the entire reconstructed
witness, by a concrete d-language embedding rather than a
source-piece naming convention. Surjectivity of the canonical
d-trace isomorphism transports the faithfulness theorem. -/
theorem faithful_sourceFull_dTraceEmbedding_irreducibleStructureFaithful
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
      (faithful_sourceFull_dTraceEmbedding
        G k S hBound hClosed hRooted B ι hFaith) := by
  have hCanonical :=
    faithful_reconstructed_sourcePiece_irreducibleStructureFaithful
      G k S hBound hClosed hRooted B ι hFaith
  intro D hD hIrr
  obtain ⟨f, hMove⟩ := hCanonical D hD hIrr
  refine ⟨f, ?_⟩
  intro z hz
  obtain ⟨p, hp⟩ := hMove z hz
  obtain ⟨x, hx⟩ :=
    (faithful_sourceSupported_dTraceEmbedding_bijective
      G k S hBound hClosed hRooted B ι hFaith).2 p
  refine ⟨x, ?_⟩
  change
    f z =
    (faithful_reconstructed_sourcePieceEmbedding
      G k S hBound hClosed hRooted B ι hFaith).toFun
      ((faithful_sourceSupported_dTraceEmbedding
        G k S hBound hClosed hRooted B ι hFaith).toFun x)
  rw [hx]
  exact hp

end AllThoseEPPA.Applications.KOrientations
