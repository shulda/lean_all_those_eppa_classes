import AllThoseEPPA.Applications.KOrientations.SecondStageRootIncomingAnchor
import AllThoseEPPA.Applications.KOrientations.CommonMoveRootRigidity
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportMonotone
import AllThoseEPPA.Applications.KOrientations.ReconstructedDigraph
import Mathlib.Data.Fintype.Card

/-!
# Projection of the complete reconstructed root outneighbourhood

Fix an auxiliary root a and a single faithful root anchor (f,r).
Every root-to-root edge a→b maps b to a root neighbour of r.
Every root-to-nonroot edge a→(x,W) maps to the non-root neighbour
g(x) of r, where g=ι.lang⁻¹*f.lang. The same anchor is used for
the entire outgoing neighbourhood; it is essential for injectivity
of this projection, proved in the next module.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

noncomputable def reconstructedRootNeighbourProjection
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : W)
    (anchor : AuxiliaryRootAnchor G k S B ι a) :
    {z : ReconstructedCarrier G k B //
      ReconstructedEdge G k B (.inl a) z} →
      G.outNeighbors anchor.source.val := by
  classical
  intro z
  obtain ⟨z,hz⟩ := z
  cases z with
  | inl b =>
      change B.rel AuxiliaryRel.edge ![a,b] at hz
      let t : RootsIn G k S :=
        Classical.choose (anchor.move_rootEdge hFaith hz)
      have hG : G.edge anchor.source.val t.val :=
        (Classical.choose_spec (anchor.move_rootEdge hFaith hz)).2
      exact ⟨t.val,(G.mem_outNeighbors anchor.source.val t.val).2 hG⟩
  | inr p =>
      change IncomingRealized G k B a p at hz
      have hs : p.support ⊆ B.closureAtSet a :=
        faithful_incoming_support_subset_closure
          G k S B ι hFaith a p hz
      have hG := anchor.move_incoming p hz hs
      exact ⟨anchor.templateMap.1 p.center,
        (G.mem_outNeighbors anchor.source.val
          (anchor.templateMap.1 p.center)).2 hG⟩

end AllThoseEPPA.Applications.KOrientations
