import AllThoseEPPA.Applications.KOrientations.ReconstructionCarrier
import AllThoseEPPA.Applications.KOrientations.FaithfulLocalTransfer

/-!
# Every canonical reconstructed support can be moved into the source

For an arbitrary vertex of the reconstructed graph, its support
is an irreducible subset of the second-stage witness B₁:

* for a root-sort vertex a it is the unary closure of {a};
* for a canonical nonroot (x,W) it is the range of a realized R_P
  relation tuple, itself already proved unary-closed in B₁.

Irreducible-structure faithfulness therefore supplies a *single*
second-stage automorphism moving the whole support into the embedded
original root sort. This is the starting point of local source
correspondences and path-lifting, and does not assert any d-class
membership.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every reconstructed support can be transported by one B₁
automorphism into the distinguished source root sort. -/
theorem faithful_reconstructed_support_movable
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (z : ReconstructedCarrier G k B) :
    ∃ f : Structure.Automorphism (auxiliaryAction G k) B,
      ∀ w ∈ reconstructedSupport G k B z,
        ∃ r : RootsIn G k S, f w = ι r := by
  cases z with
  | inl a =>
      exact faithful_moves_vertexClosure
        (auxiliaryAction G k)
        (auxiliaryRootStructure G k S) B ι hFaith a
  | inr p =>
      obtain ⟨n, P, xs, hc, hRel, hU⟩ := p.witnessed
      obtain ⟨f, hMove⟩ :=
        faithful_moves_relationClosure
          (auxiliaryAction G k)
          (auxiliaryRootStructure G k S) B ι hFaith
          (AuxiliaryRel.root P) xs hRel
      refine ⟨f, ?_⟩
      intro w hw
      apply hMove w
      apply B.subset_closureSet (Set.range xs)
      change w ∈ p.support at hw
      rw [← hU] at hw
      exact hw

end AllThoseEPPA.Applications.KOrientations
