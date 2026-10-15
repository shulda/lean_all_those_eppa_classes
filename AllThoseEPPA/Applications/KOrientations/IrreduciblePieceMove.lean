import AllThoseEPPA.Applications.KOrientations.IrreducibleRootTrace
import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceInjective
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportEquivariance

/-!
# One common B₁ automorphism moves a whole irreducible reconstructed d-piece

The root trace U of every irreducible closed reconstructed d-piece D
is an *irreducible and closed* B₁-substructure. Applying genuine
irreducible-structure faithfulness of B₁ to this root trace gives
one automorphism f such that f(U) lies in the embedded root source.

Since every reconstructed point z of D has its entire intrinsic
support contained in U, **this same automorphism f** satisfies
IsMovedSupport on every z in D simultaneously. Moving one vertex
at a time would be insufficient for irreducible-structure faithfulness.

In combination with the exact local d-isomorphisms, this is the
central common-localization step for the reconstructed faithful
EPPA theorem, still separate from constructing the final embedding A'.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every irreducible closed d-piece admits one common auxiliary
automorphism moving all of its canonical supports to the source. -/
theorem faithful_reconstructed_irreducible_piece_common_move
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
    (D : Set (ReconstructedCarrier G k B))
    (hD : (dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed D)
    (hIrr : ((dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).induce
      D hD).IsIrreducible) :
    ∃ f : Structure.Automorphism (auxiliaryAction G k) B,
      ∀ z : ReconstructedCarrier G k B,
        z ∈ D → IsMovedSupport G k S B ι f z := by
  let U : Set W := reconstructedRootTrace G k B D
  have hU : B.IsClosed U :=
    faithful_reconstructed_rootTrace_isClosed
      G k S hBound hClosed hRooted B ι hFaith D hD
  have hUIrr : (B.induce U hU).IsIrreducible :=
    faithful_reconstructed_irreducible_rootTrace
      G k S hBound hClosed hRooted B ι hFaith D hD hIrr
  obtain ⟨f, hf⟩ := hFaith U hU hUIrr
  refine ⟨f, ?_⟩
  intro z hz w hw
  have hSupport : reconstructedSupport G k B z ⊆ U :=
    (faithful_reconstructed_mem_closed_iff_support_subset_rootTrace
      G k S hBound hClosed hRooted B ι hFaith D hD z).mp hz
  obtain ⟨a, ha⟩ := hf w (hSupport hw)
  exact ⟨a, ha⟩

end AllThoseEPPA.Applications.KOrientations
