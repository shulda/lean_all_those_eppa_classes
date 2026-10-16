import AllThoseEPPA.Applications.KOrientations.ClosedRootTrace
import AllThoseEPPA.Applications.KOrientations.SecondStageRootTupleClosed

/-!
# Canonical closed pieces over auxiliary root sets

Every canonical reconstructed support is *closed in B₁*: for roots
it is a one-point closure, and for nonroots this is the exact
R_P-tuple support closure theorem.

For an arbitrary U ⊆ B₁, the piece of all reconstructed vertices
with support contained in U is d-closed. When U itself is B₁-closed,
the piece has precisely U as its root trace and is precisely the
d-closure of the tagged root set U.

This is the exact closed-pieces lemma needed in the irreducible-root
trace reduction, without any assumption that B₁ as a whole is a
rooted k-orientation.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Canonical supports are closed for the actual auxiliary unary
function of B₁, for both root and nonroot carrier summands. -/
theorem faithful_reconstructedSupport_auxiliary_isClosed
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (z : ReconstructedCarrier G k B) :
    B.IsClosed (reconstructedSupport G k B z) := by
  cases z with
  | inl a =>
      change B.IsClosed (B.closureAtSet a)
      exact B.isClosed_closureSet {a}
  | inr p =>
      change B.IsClosed p.support
      exact canonicalNonroot_support_isClosed G k S B ι hFaith p

/-- A support-defined piece is d-closed for *every* auxiliary root
subset U, even if U is not itself closed in B₁. -/
theorem faithful_reconstructed_supportedPiece_isDClosed
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
    (U : Set W) :
    (faithfulReconstructedDigraph G k S B ι hFaith).IsDClosed k
      (reconstructedSupportedPiece G k B U) := by
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  have hRootedData :=
    faithful_reconstructed_exact_roots_and_rooted
      G k S hBound hClosed hRooted B ι hFaith
  apply (H.isDClosed_iff_rootSaturated k hRootedData.1
    (reconstructedSupportedPiece G k B U)).mpr
  intro z
  constructor
  · intro hz r hr
    rw [hRootedData.2 z] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    change B.closureAtSet w ⊆ U
    have hSupportClosed : B.IsClosed (reconstructedSupport G k B z) :=
      faithful_reconstructedSupport_auxiliary_isClosed
        G k S B ι hFaith z
    have hSubset : B.closureAtSet w ⊆
        reconstructedSupport G k B z := by
      apply B.closureSet_minimal hSupportClosed
      intro t ht
      have htw : t = w := by simpa using ht
      subst t
      exact hw
    exact hSubset.trans hz
  · intro hz w hw
    have hRoot :
        (Sum.inl w : ReconstructedCarrier G k B) ∈ H.roots k z := by
      rw [hRootedData.2 z]
      exact ⟨w, hw, rfl⟩
    have hSupport :
        reconstructedSupport G k B (.inl w) ⊆ U := hz hRoot
    exact hSupport (B.mem_closureAtSet w)

/-- The support-defined piece is closed in the general exact
set-valued-function Structure API. -/
theorem faithful_reconstructed_supportedPiece_isClosed
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
    (U : Set W) :
    (dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed
      (reconstructedSupportedPiece G k B U) := by
  exact (dStructure_isClosed_iff
    (faithfulReconstructedDigraph G k S B ι hFaith) k
    (reconstructedSupportedPiece G k B U)).mpr
      (faithful_reconstructed_supportedPiece_isDClosed
        G k S hBound hClosed hRooted B ι hFaith U)

/-- If U is closed in B₁, the root trace of the supported piece is
*exactly* U, not only a subset. -/
theorem faithful_reconstructed_supportedPiece_rootTrace_eq
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (U : Set W) (hU : B.IsClosed U) :
    reconstructedRootTrace G k B
      (reconstructedSupportedPiece G k B U) = U := by
  ext a
  change B.closureAtSet a ⊆ U ↔ a ∈ U
  constructor
  · intro h
    exact h (B.mem_closureAtSet a)
  · intro ha
    apply B.closureSet_minimal hU
    intro b hb
    have hEq : b = a := by simpa using hb
    subst b
    exact ha

end AllThoseEPPA.Applications.KOrientations
