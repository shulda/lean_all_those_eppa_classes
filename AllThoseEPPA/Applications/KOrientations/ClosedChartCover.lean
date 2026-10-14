import AllThoseEPPA.Applications.KOrientations.LocalChartDClosed
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportMovable

/-!
# The reconstructed d-structure is covered by closed local charts

Irreducible-structure faithfulness of the second witness B₁ moves the
entire canonical support of any reconstructed vertex into the source.
The root-support localization theorem then shows that the full
support-moved domain for that automorphism is an honest closed
substructure of the canonical reconstructed d-structure.

Every reconstructed vertex therefore belongs to one of these
finite closed local charts. Identifying those charts with suitable
template pieces is the separate next step toward faithful EPPA.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every reconstructed point belongs to the carrier of some
automorphism-indexed *d-closed* local chart. -/
theorem faithful_reconstructed_covered_by_closed_charts
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
    (z : ReconstructedCarrier G k B) :
    ∃ f : Structure.Automorphism (auxiliaryAction G k) B,
      IsMovedSupport G k S B ι f z ∧
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed
        {w | IsMovedSupport G k S B ι f w} := by
  obtain ⟨f, hMove⟩ :=
    faithful_reconstructed_support_movable
      G k S B ι hFaith z
  refine ⟨f, hMove, ?_⟩
  exact faithful_reconstructed_local_chart_isClosed
    G k S hBound hClosed hRooted B ι hFaith f

end AllThoseEPPA.Applications.KOrientations
