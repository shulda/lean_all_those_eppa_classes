import AllThoseEPPA.Applications.KOrientations.ClosedRootTrace
import AllThoseEPPA.Applications.KOrientations.SupportIrreducibility
import AllThoseEPPA.Applications.KOrientations.NestedClosedIrreducible

/-!
# Irreducible supports cannot cross free auxiliary root decompositions

Let D be a closed reconstructed d-substructure, U=D∩B₁ its
auxiliary root trace, and z∈D. The complete support of z is a
genuinely closed, irreducible substructure of B₁ contained in U.
Consequently, if U splits as a free amalgam of two proper closed
substructures, support(z) must lie wholly in one of the sides.

This is the key support-distribution step in the manuscript's proof
that irreducibility of D forces irreducibility of U. No claim about
global reconstructed irreducible-structure faithfulness is made yet.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every reconstructed vertex of a closed d-piece has its full
intrinsic support on one side of any free decomposition of the
piece's B₁-root trace. -/
theorem faithful_reconstructedSupport_subset_one_free_root_side
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
    (d : ((B.induce (reconstructedRootTrace G k B D)
      (faithful_reconstructed_rootTrace_isClosed
        G k S hBound hClosed hRooted B ι hFaith D hD))).FreeDecomposition)
    (z : ReconstructedCarrier G k B) (hz : z ∈ D) :
    reconstructedSupport G k B z ⊆ Subtype.val '' d.left ∨
      reconstructedSupport G k B z ⊆ Subtype.val '' d.right := by
  exact irreducible_closed_subset_one_side_of_freeDecomposition
    B (reconstructedRootTrace G k B D)
    (reconstructedSupport G k B z)
    (faithful_reconstructed_rootTrace_isClosed
      G k S hBound hClosed hRooted B ι hFaith D hD)
    (faithful_reconstructedSupport_auxiliary_isClosed
      G k S B ι hFaith z)
    ((faithful_reconstructed_mem_closed_iff_support_subset_rootTrace
      G k S hBound hClosed hRooted B ι hFaith D hD z).mp hz)
    d
    (faithful_reconstructedSupport_auxiliary_isIrreducible
      G k S B ι hFaith z)

end AllThoseEPPA.Applications.KOrientations
