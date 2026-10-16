import AllThoseEPPA.Applications.KOrientations.SourceSupportedDTraceIso
import AllThoseEPPA.Applications.KOrientations.FirstStageFullDSourceEmbedding
import AllThoseEPPA.Applications.KOrientations.ReconstructedSourceFaithfulness
import AllThoseEPPA.Applications.KOrientations.EmbeddedSuccessorSourceRooted

/-!
# The actual original full d(A) source embeds in the reconstructed witness

The certified source-supported reconstructed d-piece was constructed
from the identity inverse source chart, and is bijectively isomorphic
to the INTRINSIC d-trace on S=ι[A] of the first coherent witness B₀.
The entire original d(A) is in turn bijectively isomorphic to that
exact intrinsic trace, including all higher-arity set-valued F_n.

Compose those genuine full language Structure.Embeddings with the
literal inclusion of the closed supported piece into the complete
reconstructed d-witness. The result is a FULL original d-language
embedding, not just a graph injection or a unary reduct. Its language
group component is trivial, and it preserves/reflects all edge tuples
and every set-valued F_n image exactly. Neither old S ambient d-closure
nor a nonfaithful auxiliary-language shortcut is presumed.

The selected total automorphisms still require the final pointwise
ExtendsAlong square for this composite embedding; the latter is
separately constructed from actual root/nonroot source-copy geometry.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- Honest entire ORIGINAL d(A) embedding into the whole
reconstructed full d-language, through the exact intrinsic
old-source d-trace, the canonical source-supported d-piece,
and the literal embedding of that closed piece into B. -/
noncomputable def firstStage_originalDReconstructedEmbedding
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (hBound : G.HasOutdegreeAtMost k)
    (hRooted : A.HasReachableRoots k)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) κ) :
    Structure.Embedding dTrivialAction
      (dStructure A k)
      (dStructure
        (faithfulReconstructedDigraph G k
          (Set.range ι.toFun) B κ hFaith) k) :=
  (faithful_reconstructed_sourcePieceEmbedding G k
    (Set.range ι.toFun) hBound
    (successorEmbedding_image_successorClosed A G ι)
    (successorEmbedding_image_rooted A G k hRooted ι)
    B κ hFaith).comp
  ((faithful_sourceSupported_dTraceEmbedding G k
    (Set.range ι.toFun) hBound
    (successorEmbedding_image_successorClosed A G ι)
    (successorEmbedding_image_rooted A G k hRooted ι)
    B κ hFaith).comp
      (firstStageFullDSourceEmbedding A G k ι))

end AllThoseEPPA.Applications.KOrientations
