import AllThoseEPPA.Applications.KOrientations.RootTraceClosureFormula

/-!
# Inclusion and equality of closed d-pieces are detected by root traces

The full d-closure functions make every closed reconstructed piece
root-saturated. Since reconstructed roots are *exactly* tagged
intrinsic supports, a closed piece is completely recovered from its
intersection with the genuine B₁-root sort.

This module records the resulting order embedding of the lattice of
closed d-substructures into the lattice of B₁-closed subsets.
The earlier supported-piece construction proves its surjectivity.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Containment between two closed d-substructures is equivalent to
containment of their auxiliary B₁ root traces. -/
theorem faithful_reconstructed_closed_subset_iff_rootTrace_subset
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
    (D E : Set (ReconstructedCarrier G k B))
    (hD : (dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed D)
    (hE : (dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed E) :
    D ⊆ E ↔
      reconstructedRootTrace G k B D ⊆
        reconstructedRootTrace G k B E := by
  constructor
  · intro h r hr
    exact h hr
  · intro h z hz
    apply (faithful_reconstructed_mem_closed_iff_support_subset_rootTrace
      G k S hBound hClosed hRooted B ι hFaith E hE z).mpr
    have hDmem :=
      (faithful_reconstructed_mem_closed_iff_support_subset_rootTrace
        G k S hBound hClosed hRooted B ι hFaith D hD z).mp hz
    exact hDmem.trans h

/-- Closed reconstructed d-substructures are equal if and only if
they have the same auxiliary root trace. -/
theorem faithful_reconstructed_closed_eq_iff_rootTrace_eq
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
    (D E : Set (ReconstructedCarrier G k B))
    (hD : (dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed D)
    (hE : (dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed E) :
    D = E ↔
      reconstructedRootTrace G k B D =
        reconstructedRootTrace G k B E := by
  constructor
  · intro h
    rw [h]
  · intro h
    apply Set.Subset.antisymm
    · apply (faithful_reconstructed_closed_subset_iff_rootTrace_subset
        G k S hBound hClosed hRooted B ι hFaith D E hD hE).mpr
      rw [h]
    · apply (faithful_reconstructed_closed_subset_iff_rootTrace_subset
        G k S hBound hClosed hRooted B ι hFaith E D hE hD).mpr
      rw [← h]

end AllThoseEPPA.Applications.KOrientations
