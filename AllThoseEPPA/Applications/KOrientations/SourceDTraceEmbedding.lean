import AllThoseEPPA.Applications.KOrientations.OriginalSourceChart
import AllThoseEPPA.Applications.KOrientations.LocalChartDTraceIso
import AllThoseEPPA.Substructure

/-!
# The original d-trace is embedded into the full reconstructed witness

The reconstructed source copy must be embedded as a structure in the
full d-language, not merely as a graph. The original source S is
successor-closed and rooted, but it need not be d-closed in the
ambient first-stage graph B₀; its correct domain is the *d-trace*
of B₀ on S, not the ambient induced d-substructure of B₀.

Use the exact local d-trace isomorphism for the identity auxiliary
B₁ automorphism, and compose it with literal inclusion of the
resulting genuinely d-closed chart into the reconstructed witness.

This is an actual public `Structure.Embedding dTrivialAction` and
is the designated source map for the eventual coherent EPPA theorem.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Exact source embedding into the full reconstructed d-structure.
There is no assumption that S is ambiently d-closed in B₀. -/
noncomputable def faithful_reconstructed_sourceDTrace_embedding
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
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k) := by
  let fId := Structure.Automorphism.id B
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  let T : Set (ReconstructedCarrier G k B) :=
    {z | IsMovedSupport G k S B ι fId z}
  have hT : (dStructure H k).IsClosed T :=
    faithful_reconstructed_local_chart_isClosed
      G k S hBound hClosed hRooted B ι hFaith fId
  exact (Structure.inclusion dTrivialAction (dStructure H k) T hT).comp
    (faithful_reconstructed_local_dTraceEmbedding
      G k S hBound hClosed hRooted B ι hFaith fId)

end AllThoseEPPA.Applications.KOrientations
