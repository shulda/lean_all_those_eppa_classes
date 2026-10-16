import AllThoseEPPA.Applications.KOrientations.OriginalDReconstructedEmbedding
import AllThoseEPPA.Applications.KOrientations.ReconstructedSourceFaithfulness
import AllThoseEPPA.Irreducible

/-!
# Irreducible-structure faithfulness for the ACTUAL original full d(A) source

The already certified reconstructed second witness is genuinely
irreducible-structure faithful for its canonical source-supported
d-piece, but this is not automatically the original input structure:
the original d(A) first passes through the intrinsic first-stage
d-trace and then the source-supported complete reconstructed d-piece.

Both of those intermediate structure embeddings are in fact
bijective on their exact carriers. We expose the source-independent
abstract transfer theorem: precomposing a faithful embedding with
a surjective (hence, here, bijective) structure embedding preserves
irreducible-structure faithfulness, because every required target
source-piece vertex is still the image of a genuine original vertex.

Then the ACTUAL original all-arity d(A) embedding constructed
by the exact triple composition is irreducible-structure faithful
relative to the entire reconstructed witness, with no additional
global d-closure assumption on the first-stage old-image S.
This does not yet imply coherent EPPA: the extension-along-original
embedding square remains a separate selected-action theorem.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w z t

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type z} {X : Type t}

/-- Precomposing a genuinely irreducible-structure faithful
embedding with a SOURCE-surjective full-language embedding
preserves the exact public faithful-witness condition. No
model-isomorphism or irreducibility transport lemma is assumed. -/
theorem IsIrreducibleStructureFaithful.comp_surjective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W} {C : Structure L X}
    (i : Embedding act A B) (j : Embedding act B C)
    (hj : IsIrreducibleStructureFaithful act j)
    (hi : Function.Surjective i.toFun) :
    IsIrreducibleStructureFaithful act (j.comp i) := by
  intro D hD hIrr
  obtain ⟨g,hg⟩ := hj D hD hIrr
  refine ⟨g, ?_⟩
  intro x hx
  obtain ⟨b,hgb⟩ := hg x hx
  obtain ⟨a,ha⟩ := hi b
  refine ⟨a, ?_⟩
  calc
    g x = j b := hgb
    _ = j (i a) := congrArg j.toFun ha.symm
    _ = (j.comp i) a := rfl

end Structure
end AllThoseEPPA

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- The actual original ALL-ARITY d(A) embeds as an
irreducible-structure faithful source of the COMPLETE
reconstructed d-witness, not merely the intermediate
induced source-supported piece. No global S ambient
d-closure, representative selection, or unary-only
encoding of the higher-arity F_n is used. -/
theorem firstStage_originalDReconstructedEmbedding_irreducibleFaithful
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
    Structure.IsIrreducibleStructureFaithful dTrivialAction
      (firstStage_originalDReconstructedEmbedding
        A G k hBound hRooted ι B κ hFaith) := by
  let S : Set W := Set.range ι.toFun
  let hClosed := successorEmbedding_image_successorClosed A G ι
  let hOldRooted := successorEmbedding_image_rooted A G k hRooted ι
  let e₀ := firstStageFullDSourceEmbedding A G k ι
  let e₁ := faithful_sourceSupported_dTraceEmbedding
    G k S hBound hClosed hOldRooted B κ hFaith
  let e₂ := faithful_reconstructed_sourcePieceEmbedding
    G k S hBound hClosed hOldRooted B κ hFaith
  have hSurj₀ : Function.Surjective e₀.toFun :=
    (firstStageFullDSourceEmbedding_bijective A G k ι).2
  have hSurj₁ : Function.Surjective e₁.toFun :=
    (faithful_sourceSupported_dTraceEmbedding_bijective
      G k S hBound hClosed hOldRooted B κ hFaith).2
  have hBase :
      Structure.IsIrreducibleStructureFaithful dTrivialAction e₂ :=
    faithful_reconstructed_sourcePiece_irreducibleStructureFaithful
      G k S hBound hClosed hOldRooted B κ hFaith
  change Structure.IsIrreducibleStructureFaithful dTrivialAction
    (e₂.comp (e₁.comp e₀))
  exact Structure.IsIrreducibleStructureFaithful.comp_surjective
    dTrivialAction (e₁.comp e₀) e₂ hBase
    (hSurj₁.comp hSurj₀)

end AllThoseEPPA.Applications.KOrientations
