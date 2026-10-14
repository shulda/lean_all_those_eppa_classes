import AllThoseEPPA.Applications.KOrientations.ClosedChartCover
import AllThoseEPPA.Substructure

/-!
# The complete d-closure of every reconstructed point lies in a chart

Faithfulness of the second-stage witness places every reconstructed
vertex inside a local support chart. Those charts are genuine closed
substructures of the full reconstructed d-language, not merely
successor-closed graph subsets. Consequently the entire *set-valued
function closure* of each vertex lies in the very same local chart.

This provides the one-point irreducible base case for the later
irreducible-structure-faithfulness transfer. It is not itself a proof
that every irreducible subset lies in a common chart.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every one-point d-closure can be moved into the distinguished
source chart by a single automorphism of the second witness. -/
theorem faithful_reconstructed_onePointClosure_in_chart
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
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).closureAtSet z
        ⊆ {w | IsMovedSupport G k S B ι f w} := by
  obtain ⟨f, hz, hChartClosed⟩ :=
    faithful_reconstructed_covered_by_closed_charts
      G k S hBound hClosed hRooted B ι hFaith z
  refine ⟨f, ?_⟩
  apply (dStructure
    (faithfulReconstructedDigraph G k S B ι hFaith) k).closureSet_minimal
      hChartClosed
  intro w hw
  have hEq : w = z := by
    simpa using hw
  subst w
  exact hz

end AllThoseEPPA.Applications.KOrientations
