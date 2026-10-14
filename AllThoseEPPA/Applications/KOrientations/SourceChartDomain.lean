import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportsReachable
import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceInjective
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportEquivariance

/-!
# Every transported source-copy vertex lies in its local support chart

The local correspondence c_f is defined precisely when f maps the
entire canonical support into the distinguished B₁ root-source.
Because the source-copy support is *exactly* the image of its
original reachable-root set, applying f⁻¹ to any source-copy vertex
produces a vertex in the moved-support domain for f.

This is the elementary converse needed in the eventual proof that
local correspondences are isomorphisms of closed pieces, rather than
merely injective induced graph homomorphisms.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- An inverse-moved source-copy vertex always satisfies the whole
support-movement condition for the given B₁ automorphism. -/
theorem inverseSourceCopy_isMovedSupport
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (x : {a : V // a ∈ S}) :
    IsMovedSupport G k S B ι f
      (reconstructedVertexPerm G k B f.symm
        (sourceReconstructedVertex G k S hClosed hRooted B ι x)) := by
  intro w hw
  rw [faithful_reconstructedSupport_map
    G k S B ι hFaith f.symm
    (sourceReconstructedVertex G k S hClosed hRooted B ι x)] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  rw [sourceReconstructedVertex_support_eq
    G k S hClosed hRooted B ι hFaith x] at hu
  obtain ⟨r, hr, rfl⟩ := hu
  exact ⟨r, Structure.Automorphism.apply_symm_apply f (ι r)⟩

end AllThoseEPPA.Applications.KOrientations
