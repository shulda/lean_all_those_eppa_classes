import AllThoseEPPA.Applications.KOrientations.OriginalRootImageClosed
import AllThoseEPPA.Applications.KOrientations.SupportedClosedPieces
import AllThoseEPPA.Applications.KOrientations.SourceChartBijection

/-!
# The canonical source-supported d-piece is precisely the identity chart

Let U be the image in B₁ of the original root-only source embedding.
The support-defined reconstructed piece over U is automatically
d-closed. Since the auxiliary embedding preserves all unary
function-value sets exactly, U itself is closed in B₁, so its root
trace is exactly U and the piece is the full d-closure of tagged U.

For the identity B₁ automorphism, the local moved-support condition
is *equivalent* to support containment in U. Thus the already checked
local source-copy bijection for the identity chart identifies the
complete source S with precisely this canonical source-supported
closed piece, without silently assuming ambient d-closure of S.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Membership of the fixed canonical source-supported piece agrees
exactly with the identity-automorphism local support chart. -/
theorem isMovedSupport_id_iff_source_supportedPiece
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (z : ReconstructedCarrier G k B) :
    IsMovedSupport G k S B ι (Structure.Automorphism.id B) z ↔
      z ∈ reconstructedSupportedPiece G k B (Set.range ι.toFun) := by
  have hId (w : W) :
      (Structure.Automorphism.id B) w = w := rfl
  constructor
  · intro h w hw
    obtain ⟨a, ha⟩ := h w hw
    refine ⟨a, ?_⟩
    exact (hId w ▸ ha).symm
  · intro h w hw
    obtain ⟨a, ha⟩ := h hw
    refine ⟨a, ?_⟩
    rw [hId w]
    exact ha.symm

/-- The B₁-root trace of the original source-supported closed
d-piece is exactly the embedded root source, not a proper subset. -/
theorem originalSourceSupportedPiece_rootTrace_eq
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    reconstructedRootTrace G k B
      (reconstructedSupportedPiece G k B (Set.range ι.toFun)) =
        Set.range ι.toFun := by
  exact faithful_reconstructed_supportedPiece_rootTrace_eq
    G k B (Set.range ι.toFun)
    (auxiliaryRootEmbedding_image_isClosed G k S B ι)

/-- The identity local chart and canonical source-supported piece are
literally equal as subsets of the reconstructed carrier. -/
theorem identityLocalChart_eq_sourceSupportedPiece
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    {z : ReconstructedCarrier G k B |
      IsMovedSupport G k S B ι (Structure.Automorphism.id B) z} =
    reconstructedSupportedPiece G k B (Set.range ι.toFun) := by
  ext z
  exact isMovedSupport_id_iff_source_supportedPiece G k S B ι z

end AllThoseEPPA.Applications.KOrientations
