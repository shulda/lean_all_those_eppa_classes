import AllThoseEPPA.Applications.KOrientations.SourceChartBijection
import AllThoseEPPA.Applications.KOrientations.SourceReconstructionPaths
import AllThoseEPPA.Applications.KOrientations.ReconstructionPathAction

/-!
# Inverse local source charts preserve edges and paths

The local source chart is a *bijective carrier map* from S to the
reconstructed vertices whose supports are moved into the embedded
root source by a fixed second-stage automorphism f.

Because the source-copy map preserves the four kinds of template edges
and the full reconstructed automorphism action preserves edges and
paths, the inverse chart also preserves every directed edge and path.
These are the forward halves of the closed-piece graph isomorphism.
The reverse edge implication is a separate obligation.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The inverse chart preserves oriented edges of the source graph. -/
theorem inverseSourceChart_preserves_edge
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
    (x y : {a : V // a ∈ S})
    (hxy : G.edge x.val y.val) :
    ReconstructedEdge G k B
      (inverseSourceChart G k S hClosed hRooted B ι hFaith f x).val
      (inverseSourceChart G k S hClosed hRooted B ι hFaith f y).val := by
  have hSource :
      ReconstructedEdge G k B
        (sourceReconstructedVertex G k S hClosed hRooted B ι x)
        (sourceReconstructedVertex G k S hClosed hRooted B ι y) :=
    sourceReconstructedVertex_preserves_edge
      G k S hClosed hRooted B ι x y hxy
  exact reconstructedEdge_map G k B f.symm hSource

/-- The inverse chart preserves arbitrary ambient directed paths. -/
theorem inverseSourceChart_preserves_reaches
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
    (x y : {a : V // a ∈ S})
    (hxy : G.Reaches x.val y.val) :
    (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      (inverseSourceChart G k S hClosed hRooted B ι hFaith f x).val
      (inverseSourceChart G k S hClosed hRooted B ι hFaith f y).val := by
  have hSource :
      (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
        (sourceReconstructedVertex G k S hClosed hRooted B ι x)
        (sourceReconstructedVertex G k S hClosed hRooted B ι y) := by
    exact sourceReconstructedVertex_preserves_reaches
      G k S hClosed hRooted B ι hFaith x.property hxy
  exact faithful_reconstructed_reaches_map
    G k S B ι hFaith f.symm hSource

end AllThoseEPPA.Applications.KOrientations
