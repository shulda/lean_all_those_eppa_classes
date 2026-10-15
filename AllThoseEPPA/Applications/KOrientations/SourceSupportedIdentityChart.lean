import AllThoseEPPA.Applications.KOrientations.SourceChartGraphIso
import AllThoseEPPA.Applications.KOrientations.SupportedClosedPieces
import AllThoseEPPA.EPPA

/-!
# The distinguished source-supported piece is the identity chart

The canonical source-supported reconstructed piece consists of all
vertices whose full intrinsic B₁-support lies in the embedded
original root sort. This is *exactly* the moved-support local chart
for the identity automorphism of B₁.

Consequently the already checked inverse-source chart bijection can
be instantiated with the identity to give a concrete bijection
from the template source S onto the canonical source-supported piece.
This is the correct carrier interface for the intended original
source embedding in the final coherent EPPA theorem.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The actual identity of B₁ acts as identity on vertices. -/
private theorem auxiliaryAutomorphism_id_apply
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (w : W) :
    (Structure.Automorphism.id (act := auxiliaryAction G k) B) w = w := by
  rfl

/-- The identity moved-support condition is precisely inclusion of
the intrinsic support in the embedded original root sort. -/
theorem isMovedSupport_id_iff_supportedPiece
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (z : ReconstructedCarrier G k B) :
    IsMovedSupport G k S B ι
      (Structure.Automorphism.id (act := auxiliaryAction G k) B) z ↔
        z ∈ reconstructedSupportedPiece G k B (Set.range ι.toFun) := by
  constructor
  · intro h w hw
    obtain ⟨a, ha⟩ := h w hw
    refine ⟨a, ?_⟩
    simpa only [auxiliaryAutomorphism_id_apply] using ha.symm
  · intro h w hw
    obtain ⟨a, ha⟩ := h hw
    refine ⟨a, ?_⟩
    simpa only [auxiliaryAutomorphism_id_apply] using ha.symm

/-- The support-defined source piece is exactly the local domain
for the identity B₁ automorphism, as a literal equality of sets. -/
theorem sourceSupportedPiece_eq_identityChart
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    reconstructedSupportedPiece G k B (Set.range ι.toFun) =
      {z | IsMovedSupport G k S B ι
        (Structure.Automorphism.id (act := auxiliaryAction G k) B) z} := by
  ext z
  exact (isMovedSupport_id_iff_supportedPiece G k S B ι z).symm

/-- The canonical original source and its full reconstructed
support-defined piece are in bijective correspondence. -/
noncomputable def sourceSupportedPieceEquiv
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    S ≃ {z : ReconstructedCarrier G k B //
      z ∈ reconstructedSupportedPiece G k B (Set.range ι.toFun)} := by
  let f := Structure.Automorphism.id (act := auxiliaryAction G k) B
  let e := inverseSourceChartEquiv
    G k S hClosed hRooted B ι hFaith f
  let F : S →
      {z : ReconstructedCarrier G k B //
        z ∈ reconstructedSupportedPiece G k B (Set.range ι.toFun)} :=
    fun x => ⟨(e x).val,
      (isMovedSupport_id_iff_supportedPiece G k S B ι (e x).val).mp
        (e x).property⟩
  refine Equiv.ofBijective F ?_
  constructor
  · intro x y hxy
    apply e.injective
    apply Subtype.ext
    exact congrArg Subtype.val hxy
  · intro z
    let zz : LocalReconstructedCarrier G k S B ι f :=
      ⟨z.val,
        (isMovedSupport_id_iff_supportedPiece G k S B ι z.val).mpr
          z.property⟩
    obtain ⟨x, hx⟩ := e.surjective zz
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hx

end AllThoseEPPA.Applications.KOrientations
