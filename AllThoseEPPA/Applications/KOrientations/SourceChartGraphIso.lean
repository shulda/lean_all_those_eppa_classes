import AllThoseEPPA.Applications.KOrientations.SourceChartLocalCorrespondence
import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceGraph

/-!
# Exact graph isomorphism from the source to each support-moved chart

The inverse source chart is already proved bijective, and the choice-free
local correspondence c_f is its literal inverse on source vertices.
Since c_f was independently Lean-proved to preserve *and reflect* all
four reconstructed edge clauses, the inverse source chart is an induced
graph isomorphism onto the whole support-moved local domain.

This is a full graph isomorphism, not just an injective graph
homomorphism. Later the graph-determines-functions theorem upgrades it
to the entire d-language, provided the source and chart are d-closed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The inverse source chart preserves *and reflects* every directed
edge, including both mixed-sort cases of the reconstructed graph. -/
theorem inverseSourceChart_edge_iff
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
    (x y : {v : V // v ∈ S}) :
    ReconstructedEdge G k B
      (inverseSourceChart G k S hClosed hRooted B ι hFaith f x).val
      (inverseSourceChart G k S hClosed hRooted B ι hFaith f y).val ↔
      G.edge x.val y.val := by
  have hGraph := localCorrespondence_edge_iff G k S B ι f
    (inverseSourceChart G k S hClosed hRooted B ι hFaith f x)
    (inverseSourceChart G k S hClosed hRooted B ι hFaith f y)
  rw [localCorrespondence_inverseSourceChart
        G k S hClosed hRooted B ι hFaith f x,
      localCorrespondence_inverseSourceChart
        G k S hClosed hRooted B ι hFaith f y] at hGraph
  exact hGraph

/-- The actual bijection between the source carrier and the complete
moved-support chart, with no choice of canonical quotient representatives. -/
noncomputable def inverseSourceChartEquiv
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    {v : V // v ∈ S} ≃ LocalReconstructedCarrier G k S B ι f :=
  Equiv.ofBijective
    (inverseSourceChart G k S hClosed hRooted B ι hFaith f)
    (inverseSourceChart_bijective
      G k S hClosed hRooted B ι hFaith f)

/-- The inverse chart is exactly an induced-graph isomorphism between
the full source and the moved-support portion of the reconstructed
graph. -/
theorem inverseSourceChartEquiv_edge_iff
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
    (x y : {v : V // v ∈ S}) :
    G.edge x.val y.val ↔
      (faithfulReconstructedDigraph G k S B ι hFaith).edge
        ((inverseSourceChartEquiv G k S hClosed hRooted B ι hFaith f x).val)
        ((inverseSourceChartEquiv G k S hClosed hRooted B ι hFaith f y).val) := by
  exact (inverseSourceChart_edge_iff
    G k S hClosed hRooted B ι hFaith f x y).symm

end AllThoseEPPA.Applications.KOrientations
