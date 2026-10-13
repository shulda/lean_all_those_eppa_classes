import AllThoseEPPA.Applications.KOrientations.SourceReconstructionVertex
import AllThoseEPPA.Applications.KOrientations.ReconstructedDigraph

/-!
# Source paths lift into the reconstructed directed graph

The source-copy map preserves all four individual edge clauses.
Since the source S is successor-closed, the intermediate vertices of
any directed path starting in S also lie in S. Hence every such path
has an actual lift to the reconstructed graph, using the same
source-copy map at every vertex.

No identification of the final root sort or of higher d-functions
is used here.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every directed path in a successor-closed distinguished source
is mapped to a directed path in the genuine reconstructed Digraph. -/
theorem sourceReconstructedVertex_preserves_reaches
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {x y : V} (hx : x ∈ S) (h : G.Reaches x y) :
    (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      (sourceReconstructedVertex G k S hClosed hRooted B ι ⟨x,hx⟩)
      (sourceReconstructedVertex G k S hClosed hRooted B ι
        ⟨y, hClosed x y hx h⟩) := by
  induction h generalizing hx with
  | refl a =>
      exact Digraph.Reaches.refl _
  | @step a b c hEdge hRest ih =>
      have hb : b ∈ S :=
        hClosed a b hx (G.reaches_of_edge hEdge)
      have hSourceEdge :
          ReconstructedEdge G k B
            (sourceReconstructedVertex G k S hClosed hRooted B ι
              ⟨a,hx⟩)
            (sourceReconstructedVertex G k S hClosed hRooted B ι
              ⟨b,hb⟩) :=
        sourceReconstructedVertex_preserves_edge
          G k S hClosed hRooted B ι ⟨a,hx⟩ ⟨b,hb⟩ hEdge
      have hGraphEdge :
          (faithfulReconstructedDigraph G k S B ι hFaith).edge
            (sourceReconstructedVertex G k S hClosed hRooted B ι
              ⟨a,hx⟩)
            (sourceReconstructedVertex G k S hClosed hRooted B ι
              ⟨b,hb⟩) :=
        hSourceEdge
      exact Digraph.Reaches.step hGraphEdge (ih hb)

end AllThoseEPPA.Applications.KOrientations
