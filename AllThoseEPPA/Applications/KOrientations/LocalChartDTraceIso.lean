import AllThoseEPPA.Applications.KOrientations.SourceChartGraphIso
import AllThoseEPPA.Applications.KOrientations.LocalChartDClosed
import AllThoseEPPA.Applications.KOrientations.ClosedGraphDTraceIso

/-!
# Full local d-isomorphisms without ambient d-closure of the source

The source-copy chart is a bijective graph isomorphism between S and a
canonical support-moved local domain of the reconstructed graph. Under
the actual hypotheses (bounded-degree B₀, rooted successor-closed S,
faithful auxiliary embedding into B₁), the target chart is truly
d-closed in the reconstructed witness.

No hypothesis of S being d-closed in the whole first-stage B₀ is
used: the source carries its canonical d-trace, namely ambient
d-function values restricted to S. Graph-determined function
transport gives a genuine exact bijective embedding between this
source d-trace and the induced target d-substructure.

This precise formulation avoids falsely assuming first-stage
d-closure and is the relevant local model for the second-stage
irreducible-structure-faithfulness proof.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Each source d-trace is genuinely isomorphic to its corresponding
closed reconstructed local support chart, in the complete d-language. -/
noncomputable def faithful_reconstructed_local_dTraceEmbedding
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Structure.Embedding dTrivialAction
      (dTraceStructure G k S)
      ((dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).induce
        {z | IsMovedSupport G k S B ι f z}
        (faithful_reconstructed_local_chart_isClosed
          G k S hBound hClosed hRooted B ι hFaith f)) := by
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  let T : Set (ReconstructedCarrier G k B) :=
    {z | IsMovedSupport G k S B ι f z}
  let e := inverseSourceChartEquiv
    G k S hClosed hRooted B ι hFaith f
  have hTSucc : ∀ (x y : ReconstructedCarrier G k B),
      x ∈ T → H.edge x y → y ∈ T := by
    intro x y hx hxy
    exact isMovedSupport_of_reconstructed_edge
      G k S B ι hFaith f hx hxy
  have hSSucc : ∀ (x y : V),
      x ∈ S → G.edge x y → y ∈ S := by
    intro x y hx hxy
    exact hClosed x y hx (G.reaches_of_edge hxy)
  have hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val := by
    intro x y
    exact inverseSourceChartEquiv_edge_iff
      G k S hClosed hRooted B ι hFaith f x y
  exact closedGraph_dTraceEmbedding
    G H k S T hSSucc hTSucc e hEdge

/-- The induced local embedding is surjective, so it is a full
bijection between the d-trace and the closed target substructure. -/
theorem faithful_reconstructed_local_dTraceEmbedding_bijective
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Function.Bijective
      (faithful_reconstructed_local_dTraceEmbedding
        G k S hBound hClosed hRooted B ι hFaith f).toFun := by
  exact (inverseSourceChartEquiv
    G k S hClosed hRooted B ι hFaith f).bijective

end AllThoseEPPA.Applications.KOrientations
