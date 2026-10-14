import AllThoseEPPA.Applications.KOrientations.DStructurePermEquivariance
import AllThoseEPPA.Applications.KOrientations.ReconstructedDigraph
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdgeAction

/-!
# The second-stage action is an action on the full reconstructed d-language

The full second-stage automorphism group acts on reconstructed vertices
by the checked choice-free tagged permutation. All four edge clauses
were proved invariant under it. The generic all-arity d-transport
theorem then proves exact equivariance of the *entire* d-expansion:
directed edges, unary reachability and all positive-arity fibres.

Crucially this does not use a quotient/lift of the template action,
nor any unproved EPPA-gluing property. It is a property of each
already-existing second-stage automorphism.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

private theorem reconstructed_graph_perm_edge_iff
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (x y : ReconstructedCarrier G k B) :
    (faithfulReconstructedDigraph G k S B ι hFaith).edge
      (reconstructedVertexPerm G k B f x)
      (reconstructedVertexPerm G k B f y) ↔
    (faithfulReconstructedDigraph G k S B ι hFaith).edge x y :=
  (reconstructedEdge_iff_map G k B f x y).symm

/-- The B₁ automorphism action preserves and reflects every relation
of the reconstructed full d-structure. -/
theorem faithful_reconstructed_d_rel_map_iff
    {V : Type u} [Fintype V] {W : Type v} [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {n : ℕ} (R : EdgeSymbol n)
    (xs : Fin n → ReconstructedCarrier G k B) :
    (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k).rel
        R (reconstructedVertexPerm G k B f ∘ xs) ↔
      (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k).rel
        R xs := by
  exact dStructure_rel_perm_iff
    (faithfulReconstructedDigraph G k S B ι hFaith) k
    (reconstructedVertexPerm G k B f)
    (reconstructed_graph_perm_edge_iff G k S B ι hFaith f) R xs

/-- The entire set of outputs of each d-function is transported
exactly by B₁ automorphisms, including arbitrary-arity root fibres. -/
theorem faithful_reconstructed_d_func_image
    {V : Type u} [Fintype V] {W : Type v} [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {n : ℕ} (F : DFunctionSymbol n)
    (xs : Fin n → ReconstructedCarrier G k B) :
    (reconstructedVertexPerm G k B f) ''
      (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k).func
        F xs =
      (dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k).func
        F (reconstructedVertexPerm G k B f ∘ xs) := by
  exact dStructure_func_image_perm
    (faithfulReconstructedDigraph G k S B ι hFaith) k
    (reconstructedVertexPerm G k B f)
    (reconstructed_graph_perm_edge_iff G k S B ι hFaith f) F xs

end AllThoseEPPA.Applications.KOrientations
