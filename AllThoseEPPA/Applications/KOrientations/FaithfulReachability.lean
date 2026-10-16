import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulGraph

/-!
# Transport directed paths in the faithful first-stage witness

Graph reachability is invariant under both exact embeddings
from the original oriented graph and total automorphisms
of the faithful witness. This is used to prove that the
witness's unary successor values contain *exactly* its
graph-theoretic reachable vertices.

The result is independent of any out-degree bound or of
equality between the successor function and reachability.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Exact source embeddings transport each directed edge. -/
private theorem faithful_edge_of_source
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    {a b : α} (hab : G.edge a b) :
    (faithfulWitnessDigraph G B ι hFaith).edge (ι a) (ι b) := by
  change B.rel EdgeSymbol.edge ![ι a, ι b]
  have hSource :
      (successorStructure G).rel EdgeSymbol.edge ![a, b] := hab
  have hRel := (ι.map_rel_iff EdgeSymbol.edge ![a, b]).2 hSource
  have htup : (ι.toFun ∘ ![a, b]) = ![ι a, ι b] := by
    funext i
    fin_cases i <;> rfl
  rw [htup] at hRel
  simpa only [successorAction_on_edge] using hRel

/-- Total automorphisms transport each directed edge. -/
private theorem faithful_edge_of_automorphism
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    (g : Structure.Automorphism successorAction B)
    {x y : β}
    (h : (faithfulWitnessDigraph G B ι hFaith).edge x y) :
    (faithfulWitnessDigraph G B ι hFaith).edge (g x) (g y) := by
  change B.rel EdgeSymbol.edge ![g x, g y]
  have hRel := (Structure.Automorphism.map_rel_iff
    g EdgeSymbol.edge ![x, y]).2 h
  have htup : (g ∘ ![x, y]) = ![g x, g y] := by
    funext i
    fin_cases i <;> rfl
  rw [htup] at hRel
  simpa only [successorAction_on_edge] using hRel

/-- Reachability in the source graph lifts to reachability in
the graph reconstructed from the faithful unary witness. -/
theorem faithful_reaches_of_source
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    {a b : α} (hab : G.Reaches a b) :
    (faithfulWitnessDigraph G B ι hFaith).Reaches (ι a) (ι b) := by
  induction hab with
  | refl a =>
      exact Digraph.Reaches.refl (ι a)
  | step h _ ih =>
      exact Digraph.Reaches.step
        (faithful_edge_of_source G B ι hFaith h) ih

/-- A total automorphism of the faithful witness transports
every finite directed path of the induced graph. -/
theorem faithful_automorphism_reaches
    {α : Type u} {β : Type v}
    (G : Digraph α) (B : Structure successorLanguage β)
    (ι : Structure.Embedding successorAction (successorStructure G) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful successorAction ι)
    (g : Structure.Automorphism successorAction B)
    {x y : β}
    (hxy : (faithfulWitnessDigraph G B ι hFaith).Reaches x y) :
    (faithfulWitnessDigraph G B ι hFaith).Reaches (g x) (g y) := by
  induction hxy with
  | refl x =>
      exact Digraph.Reaches.refl (g x)
  | step h _ ih =>
      exact Digraph.Reaches.step
        (faithful_edge_of_automorphism G B ι hFaith g h) ih

end AllThoseEPPA.Applications.KOrientations
