import AllThoseEPPA.Applications.KOrientations.RootTraceOrder
import AllThoseEPPA.Applications.KOrientations.SupportedClosedPieces

/-!
# Exact correspondence of closed d-substructures and B₁-root substructures

A d-closed vertex set of the reconstructed orientation is completely
determined by its genuine B₁-root trace. Conversely, each auxiliary
B₁-closed set U determines a canonical d-closed supported piece,
and that piece has root trace exactly U.

These two constructions are inverse. We package them as a concrete
equivalence of the carriers of the lattices of closed substructures,
preserving and reflecting inclusion. This is a reusable interface for
the irreducibility transfer and for later exact-domain restrictions.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Root trace and full supported-piece reconstruction are inverse
bijections between closed reconstructed d-pieces and auxiliary B₁-
closed root sets, without finiteness of their *families*. -/
noncomputable def faithful_reconstructed_closedRootTraceEquiv
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
    {D : Set (ReconstructedCarrier G k B) //
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed D} ≃
    {U : Set W // B.IsClosed U} where
  toFun := fun D =>
    ⟨reconstructedRootTrace G k B D.val,
      faithful_reconstructed_rootTrace_isClosed
        G k S hBound hClosed hRooted B ι hFaith
        D.val D.property⟩
  invFun := fun U =>
    ⟨reconstructedSupportedPiece G k B U.val,
      faithful_reconstructed_supportedPiece_isClosed
        G k S hBound hClosed hRooted B ι hFaith
        U.val⟩
  left_inv := by
    intro D
    apply Subtype.ext
    exact (faithful_reconstructed_closed_eq_supportedPiece
      G k S hBound hClosed hRooted B ι hFaith
      D.val D.property).symm
  right_inv := by
    intro U
    apply Subtype.ext
    exact faithful_reconstructed_supportedPiece_rootTrace_eq
      G k B U.val U.property

/-- The root-trace equivalence identifies the inclusion order of
closed d-substructures with the inclusion order of auxiliary
B₁-closed substructures. -/
theorem faithful_reconstructed_closedRootTraceEquiv_subset_iff
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
    (D E : {T : Set (ReconstructedCarrier G k B) //
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed T}) :
    D.val ⊆ E.val ↔
      (faithful_reconstructed_closedRootTraceEquiv
        G k S hBound hClosed hRooted B ι hFaith D).val ⊆
      (faithful_reconstructed_closedRootTraceEquiv
        G k S hBound hClosed hRooted B ι hFaith E).val :=
  faithful_reconstructed_closed_subset_iff_rootTrace_subset
    G k S hBound hClosed hRooted B ι hFaith
    D.val E.val D.property E.property

end AllThoseEPPA.Applications.KOrientations
