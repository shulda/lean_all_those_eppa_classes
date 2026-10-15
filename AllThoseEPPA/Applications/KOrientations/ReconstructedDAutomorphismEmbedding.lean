import AllThoseEPPA.Applications.KOrientations.ReconstructedDStructureAction
import AllThoseEPPA.Applications.KOrientations.ClosedGraphDInducedIso

/-!
# Full reconstructed d-structure embeddings from auxiliary automorphisms

The canonical second-stage vertex permutation is already known to
preserve and reflect the four graph edge clauses, and to transport
every set-valued function of the complete d-language exactly.

Package this as a *real* `Structure.Embedding` for the trivial
d-language action, with bijective carrier map. This avoids appealing
only to separate pointwise transport lemmas when constructing the
eventual faithful coherent EPPA extension.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every genuine auxiliary B₁-automorphism induces a bijective
embedding of the complete canonical reconstructed d-structure. -/
noncomputable def faithful_reconstructed_dEmbedding_of_auxAutomorphism
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Structure.Embedding dTrivialAction
      (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k)
      (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k) where
  lang := 1
  toFun := reconstructedVertexPerm G k B f
  injective := (reconstructedVertexPerm G k B f).injective
  map_rel_iff := by
    intro n R xs
    change (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).rel
        R (reconstructedVertexPerm G k B f ∘ xs) ↔
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).rel R xs
    exact faithful_reconstructed_d_rel_map_iff
      G k S B ι hFaith f R xs
  map_func := by
    intro n F xs
    change (reconstructedVertexPerm G k B f) ''
        (dStructure
          (faithfulReconstructedDigraph G k S B ι hFaith) k).func F xs =
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).func
        F (reconstructedVertexPerm G k B f ∘ xs)
    exact faithful_reconstructed_d_func_image
      G k S B ι hFaith f F xs

/-- The induced map is a permutation, hence surjective as well. -/
theorem faithful_reconstructed_dEmbedding_of_auxAutomorphism_bijective
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Function.Bijective
      (faithful_reconstructed_dEmbedding_of_auxAutomorphism
        G k S B ι hFaith f).toFun :=
  (reconstructedVertexPerm G k B f).bijective

end AllThoseEPPA.Applications.KOrientations
