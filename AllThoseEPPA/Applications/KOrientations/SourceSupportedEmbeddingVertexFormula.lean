import AllThoseEPPA.Applications.KOrientations.SourceSupportedIdentityChart
import AllThoseEPPA.Applications.KOrientations.SourceSupportedDTraceIso
import AllThoseEPPA.Applications.KOrientations.ReconstructionVertexAction

/-!
# Actual canonical source embedding equals the literal source-reconstruction map

The source-supported piece is the identity inverse-source chart.
The chosen source map used in all original edge/closure arguments,
however, was previously written as the literal sourceReconstructedVertex.

We remove this representational mismatch: the reconstructed B₁
identity automorphism acts as literal identity on BOTH root and
canonical nonroot sorts. Its reverse action does too, by the
certified inverse-law. Hence the value of the original source
supported-piece equivalence is literally sourceReconstructedVertex.

This is a genuine pointwise statement on the full reconstructed
carrier, not just equality of root/support group coordinates or
identification of different vertices. In particular, all
nonroots retain the canonical (centre, support) representation.
It is the API needed for the honest all-arity original d(A)
embedding extension square with the actually chosen two-stage
coherent automorphism.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The ACTUAL identity auxiliary B₁ automorphism induces
the literal identity reconstructed vertex permutation on
both sorts, including all realized canonical nonroot pairs. -/
theorem reconstructedVertexPerm_id_apply
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (z : ReconstructedCarrier G k B) :
    reconstructedVertexPerm G k B
      (Structure.Automorphism.id (act := auxiliaryAction G k) B) z = z := by
  let f := Structure.Automorphism.id (act := auxiliaryAction G k) B
  cases z with
  | inl a =>
      change Sum.inl (f a) = Sum.inl a
      rfl
  | inr p =>
      change Sum.inr (CanonicalNonroot.map f p) = Sum.inr p
      congr 1
      apply CanonicalNonroot.eq_of_center_support
      · change f.lang.1 p.center = p.center
        change (1 : G.graphAut).1 p.center = p.center
        simp
      · change f '' p.support = p.support
        ext w
        constructor
        · rintro ⟨x, hx, hxw⟩
          have hId : f x = x := rfl
          rw [hId] at hxw
          exact hxw ▸ hx
        · intro hw
          exact ⟨w, hw, show f w = w from rfl⟩

/-- The literal ORIGINAL source point in the reconstructed
witness is exactly the value of the genuine canonical
supported-piece bijection, including for nonroot vertices.
No identifying different centres by equal root supports. -/
theorem sourceSupportedPieceEquiv_val_eq_sourceReconstructedVertex
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (x : S) :
    (sourceSupportedPieceEquiv
      G k S hClosed hRooted B ι hFaith x).val =
      sourceReconstructedVertex G k S hClosed hRooted B ι x := by
  let f := Structure.Automorphism.id (act := auxiliaryAction G k) B
  let z := sourceReconstructedVertex G k S hClosed hRooted B ι x
  have hInv : reconstructedVertexPerm G k B f.symm
      (reconstructedVertexPerm G k B f z) = z :=
    reconstructedVertexPerm_symm_map G k B f z
  have hId : reconstructedVertexPerm G k B f z = z :=
    reconstructedVertexPerm_id_apply G k B z
  rw [hId] at hInv
  change reconstructedVertexPerm G k B f.symm z = z
  exact hInv

end AllThoseEPPA.Applications.KOrientations
