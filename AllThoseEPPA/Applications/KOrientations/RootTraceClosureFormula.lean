import AllThoseEPPA.Applications.KOrientations.SupportedClosedPieces

/-!
# Exact d-closure of an auxiliary root substructure

When U is closed in B₁, its canonical supported piece in the
reconstructed d-structure is exactly the *function closure*
of tagged U. The proof uses the root-saturation characterization
of d-closed substructures and the exact equality between
reachable reconstructed roots and intrinsic canonical supports.

Consequently every d-closed reconstructed substructure is
the closure of its root trace D ∩ B₁, and this trace is genuinely
closed in the auxiliary root structure B₁.

These are the explicit closed-pieces facts preceding the
irreducibility-root projection in the manuscript.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A supported piece above an auxiliary closed root set U is exactly
the d-closure of U, embedded as tagged reconstructed roots. -/
theorem faithful_reconstructed_supportedPiece_eq_rootClosure
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
    (U : Set W) (hU : B.IsClosed U) :
    reconstructedSupportedPiece G k B U =
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).closureSet
        ((Sum.inl : W → ReconstructedCarrier G k B) '' U) := by
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  let T : Set (ReconstructedCarrier G k B) :=
    (Sum.inl : W → ReconstructedCarrier G k B) '' U
  have hRootedData :=
    faithful_reconstructed_exact_roots_and_rooted
      G k S hBound hClosed hRooted B ι hFaith
  apply Set.Subset.antisymm
  · intro z hz
    apply H.mem_of_roots_subset_isDClosed k hRootedData.1
      ((dStructure_isClosed_iff H k
        ((dStructure H k).closureSet T)).mp
          ((dStructure H k).isClosed_closureSet T))
    intro r hr
    rw [hRootedData.2 z] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    apply (dStructure H k).subset_closureSet T
    exact ⟨w, hz hw, rfl⟩
  · apply (dStructure H k).closureSet_minimal
      (faithful_reconstructed_supportedPiece_isClosed
        G k S hBound hClosed hRooted B ι hFaith U)
    intro r hr
    obtain ⟨w, hw, rfl⟩ := hr
    change B.closureAtSet w ⊆ U
    apply B.closureSet_minimal hU
    intro t ht
    have hEq : t = w := by simpa using ht
    subst t
    exact hw

/-- Every genuinely d-closed reconstructed substructure is the
complete d-closure of its genuine auxiliary root trace. -/
theorem faithful_reconstructed_closed_eq_rootTraceClosure
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
      (faithfulReconstructedDigraph G k S B ι hFaith) k).IsClosed D) :
    D =
      (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).closureSet
        ((Sum.inl : W → ReconstructedCarrier G k B) ''
          reconstructedRootTrace G k B D) := by
  let U := reconstructedRootTrace G k B D
  have hU : B.IsClosed U :=
    faithful_reconstructed_rootTrace_isClosed
      G k S hBound hClosed hRooted B ι hFaith D hD
  calc
    D = reconstructedSupportedPiece G k B U :=
      faithful_reconstructed_closed_eq_supportedPiece
        G k S hBound hClosed hRooted B ι hFaith D hD
    _ = (dStructure
        (faithfulReconstructedDigraph G k S B ι hFaith) k).closureSet
        ((Sum.inl : W → ReconstructedCarrier G k B) '' U) :=
      faithful_reconstructed_supportedPiece_eq_rootClosure
        G k S hBound hClosed hRooted B ι hFaith U hU

end AllThoseEPPA.Applications.KOrientations
