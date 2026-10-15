import AllThoseEPPA.Applications.KOrientations.SourceSupportedIdentityChart
import AllThoseEPPA.Applications.KOrientations.ClosedGraphDTraceIso

/-!
# Canonical d-trace isomorphism onto the source-supported d-piece

The canonical source-supported reconstructed piece is literally the
identity local chart. The induced source chart graph equivalence
therefore preserves and reflects the complete directed graph.

The source need not be d-closed in the first-stage ambient witness:
its intrinsic d-trace is mapped to the genuinely d-closed canonical
source-supported piece of the final reconstruction.

This is the explicit structure-map interface needed to identify the
initial A with the embedded copy A' inside the reconstructed witness.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The complete intrinsic source d-language embeds bijectively into
the genuine induced d-substructure over original B₁-root points. -/
noncomputable def faithful_sourceSupported_dTraceEmbedding
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    Structure.Embedding dTrivialAction
      (dTraceStructure G k S)
      ((dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).induce
        (reconstructedSupportedPiece G k B (Set.range ι.toFun))
        (faithful_reconstructed_supportedPiece_isClosed
          G k S hBound hClosed hRooted B ι hFaith
          (Set.range ι.toFun))) := by
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  let T : Set (ReconstructedCarrier G k B) :=
    reconstructedSupportedPiece G k B (Set.range ι.toFun)
  let f := Structure.Automorphism.id (act := auxiliaryAction G k) B
  let e := sourceSupportedPieceEquiv
    G k S hClosed hRooted B ι hFaith
  have hS : ∀ x y : V, x ∈ S → G.edge x y → y ∈ S := by
    intro x y hx hxy
    exact hClosed x y hx (G.reaches_of_edge hxy)
  have hTD : H.IsDClosed k T :=
    faithful_reconstructed_supportedPiece_isDClosed
      G k S hBound hClosed hRooted B ι hFaith
      (Set.range ι.toFun)
  have hT : ∀ x y : ReconstructedCarrier G k B,
      x ∈ T → H.edge x y → y ∈ T := by
    intro x y hx hxy
    exact hTD.1 x y hx (H.reaches_of_edge hxy)
  have hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val := by
    intro x y
    change G.edge x.val y.val ↔
      H.edge
        ((inverseSourceChartEquiv
          G k S hClosed hRooted B ι hFaith f) x).val
        ((inverseSourceChartEquiv
          G k S hClosed hRooted B ι hFaith f) y).val
    exact inverseSourceChartEquiv_edge_iff
      G k S hClosed hRooted B ι hFaith f x y
  have hTrace :
      dTraceStructure H k T =
        (dStructure H k).induce T
          ((dStructure_isClosed_iff H k T).mpr hTD) :=
    dTraceStructure_eq_induce_of_dClosed H k T hTD
  change Structure.Embedding dTrivialAction
      (dTraceStructure G k S)
      ((dStructure H k).induce T
        (faithful_reconstructed_supportedPiece_isClosed
          G k S hBound hClosed hRooted B ι hFaith
          (Set.range ι.toFun)))
  rw [← hTrace]
  exact closedGraph_dTraceEmbedding G H k S T hS hT e hEdge

/-- The canonical source d-trace embedding is bijective on vertices. -/
theorem faithful_sourceSupported_dTraceEmbedding_bijective
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    Function.Bijective
      (faithful_sourceSupported_dTraceEmbedding
        G k S hBound hClosed hRooted B ι hFaith).toFun := by
  exact (sourceSupportedPieceEquiv
    G k S hClosed hRooted B ι hFaith).bijective

end AllThoseEPPA.Applications.KOrientations
