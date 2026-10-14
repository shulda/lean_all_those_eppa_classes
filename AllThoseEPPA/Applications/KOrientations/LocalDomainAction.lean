import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceInjective
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportEquivariance

/-!
# Functoriality of the locally moved-support domains

The local domain for an automorphism f of B₁ consists of vertices whose
*entire* canonical support is carried by f into the embedded root
source. Transporting a vertex first by another B₁ automorphism g
changes this condition exactly to the local condition for f ∘ g.

This is a concrete, choice-free compatibility statement for the
local charts used in faithful coherent EPPA gluing. No global
faithfulness or d-membership of the reconstruction is assumed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The local-support domain transforms contravariantly when
composing two actual second-stage automorphisms. -/
theorem isMovedSupport_vertexPerm_iff_comp
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f g : Structure.Automorphism (auxiliaryAction G k) B)
    (z : ReconstructedCarrier G k B) :
    IsMovedSupport G k S B ι f
        (reconstructedVertexPerm G k B g z) ↔
      IsMovedSupport G k S B ι (f.comp g) z := by
  change
    (∀ w ∈ reconstructedSupport G k B
      (reconstructedVertexPerm G k B g z),
      ∃ t : RootsIn G k S, f w = ι t) ↔
    (∀ w ∈ reconstructedSupport G k B z,
      ∃ t : RootsIn G k S, (f.comp g) w = ι t)
  rw [faithful_reconstructedSupport_map G k S B ι hFaith g z]
  constructor
  · intro hm w hw
    obtain ⟨t, ht⟩ := hm (g w) ⟨w, hw, rfl⟩
    refine ⟨t, ?_⟩
    simpa only [Structure.Automorphism.comp_apply] using ht
  · intro hm w hw
    obtain ⟨v, hv, hgw⟩ := hw
    subst w
    obtain ⟨t, ht⟩ := hm v hv
    refine ⟨t, ?_⟩
    simpa only [Structure.Automorphism.comp_apply] using ht

end AllThoseEPPA.Applications.KOrientations
