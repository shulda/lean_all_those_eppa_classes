import AllThoseEPPA.Applications.KOrientations.FullDAutomorphism

/-!
# Composition of the genuine reconstructed d-automorphisms

The canonical second-stage action was proved coordinatewise
functorial on the reconstructed tagged vertex type. The preceding
module packages each such permutation as a *total* automorphism of
the complete d-structure in the public EPPA API.

This module upgrades the pointwise group action law to literal
equality of the public `Structure.Automorphism` objects, including
the language group component. This is the algebraic composition
identity required in the eventual coherent selector; the separate
extension/gluing assertion remains open.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The passage from actual B₁ automorphisms to reconstructed
full d-automorphisms preserves ordered composition exactly. -/
theorem faithful_reconstructed_dAutomorphism_comp
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f g : Structure.Automorphism (auxiliaryAction G k) B) :
    faithful_reconstructed_dAutomorphism_of_auxAutomorphism
      G k S B ι hFaith (f.comp g) =
    (faithful_reconstructed_dAutomorphism_of_auxAutomorphism
      G k S B ι hFaith f).comp
    (faithful_reconstructed_dAutomorphism_of_auxAutomorphism
      G k S B ι hFaith g) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · exact Subsingleton.elim _ _
  · intro z
    have hAction := reconstructedVertexPerm_comp G k B f g
    calc
      faithful_reconstructed_dAutomorphism_of_auxAutomorphism
          G k S B ι hFaith (f.comp g) z =
          reconstructedVertexPerm G k B (f.comp g) z :=
        faithful_reconstructed_dAutomorphism_apply
          G k S B ι hFaith (f.comp g) z
      _ = reconstructedVertexPerm G k B f
          (reconstructedVertexPerm G k B g z) := by
        have h := congrArg
          (fun p : Equiv.Perm (ReconstructedCarrier G k B) => p z)
          hAction
        simpa using h
      _ = (faithful_reconstructed_dAutomorphism_of_auxAutomorphism
          G k S B ι hFaith f).comp
          (faithful_reconstructed_dAutomorphism_of_auxAutomorphism
            G k S B ι hFaith g) z := by
        simp only [Structure.Automorphism.comp_apply,
          faithful_reconstructed_dAutomorphism_apply]

end AllThoseEPPA.Applications.KOrientations
