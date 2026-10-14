import AllThoseEPPA.Applications.KOrientations.SourceChartGraphIso
import AllThoseEPPA.Applications.KOrientations.LocalChartDClosed
import AllThoseEPPA.Applications.KOrientations.ClosedGraphDInducedIso

/-!
# Exact full d-language isomorphism of every reconstructed local chart

The source-copy chart is a bijective induced graph isomorphism onto
the canonical support-moved domain. Under the genuine first-stage
source hypotheses that S is successor-closed, rooted and d-closed,
the reconstructed local chart is also d-closed by the checked
root/support identity.

The general graph-determines-functions theorem therefore promotes
this concrete chart to an *exact bijective Structure.Embedding* of
the full d-language. All positive-arity F_n and the unary reachability
function are transported exactly, including their entire value sets.

This is a local isomorphism statement. It does not yet assert global
irreducible-structure faithfulness or coherent EPPA.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The canonical source-copy map is a bijective, d-function-exact
embedding of its induced d-structure onto the full local support chart. -/
noncomputable def faithful_reconstructed_local_dEmbedding
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (hSourceDClosed : G.IsDClosed k S)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Structure.Embedding dTrivialAction
      ((dStructure G k).induce S
        ((dStructure_isClosed_iff G k S).mpr hSourceDClosed))
      ((dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).induce
          {z | IsMovedSupport G k S B ι f z}
          (faithful_reconstructed_local_chart_isClosed
            G k S hBound hClosed hRooted B ι hFaith f)) := by
  let e := inverseSourceChartEquiv
    G k S hClosed hRooted B ι hFaith f
  have hTargetDClosed :
      (faithfulReconstructedDigraph G k S B ι hFaith).IsDClosed
        k {z | IsMovedSupport G k S B ι f z} :=
    faithful_reconstructed_local_chart_isDClosed
      G k S hBound hClosed hRooted B ι hFaith f
  have hEdge : ∀ x y : {v : V // v ∈ S},
      G.edge x.val y.val ↔
        (faithfulReconstructedDigraph G k S B ι hFaith).edge
          (e x).val (e y).val := by
    intro x y
    exact inverseSourceChartEquiv_edge_iff
      G k S hClosed hRooted B ι hFaith f x y
  exact closedGraph_inducedDIsomorphism
    G (faithfulReconstructedDigraph G k S B ι hFaith) k
    S {z | IsMovedSupport G k S B ι f z}
    hSourceDClosed hTargetDClosed e hEdge

/-- Its vertex map is surjective as well as injective, so the
constructed local d-embedding is genuinely an isomorphism. -/
theorem faithful_reconstructed_local_dEmbedding_bijective
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (hSourceDClosed : G.IsDClosed k S)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Function.Bijective
      (faithful_reconstructed_local_dEmbedding
        G k S hBound hClosed hRooted hSourceDClosed
        B ι hFaith f).toFun := by
  exact (inverseSourceChartEquiv
    G k S hClosed hRooted B ι hFaith f).bijective

end AllThoseEPPA.Applications.KOrientations
