import AllThoseEPPA.Applications.KOrientations.ReconstructionRootSupportCriterion
import AllThoseEPPA.Applications.KOrientations.ReconstructionExactDegrees
import AllThoseEPPA.Applications.KOrientations.Encoding

/-!
# Exact d-closure class membership from constructive support paths

The reconstructed graph already has the k-orientation axioms and,
for a successor-closed rooted source, exactly the B₁ vertices as
its k-roots. One final constructive obligation is the ability to
reach every root in the canonical support of any reconstructed vertex.

This module isolates that obligation and proves that it suffices:
the reconstructed orientation then has nonempty root sets, each
computed root set is exactly the tagged canonical support, and its
exact d-language expansion is the standard `dStructure`.

No version of this theorem silently assumes path lifting. It is an
explicit hypothesis to be proved from the source-copy construction.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Under the actual source hypotheses and constructive support-path
lifting, the reconstructed graph belongs to the rooted k-orientation
class and has exactly the expected canonical root sets. -/
theorem faithful_reconstructed_rooted_and_exact_support
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRootedS : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (hLift : ∀ (z : ReconstructedCarrier G k B) (r : W),
      r ∈ reconstructedSupport G k B z →
      (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
        z (.inl r)) :
    (faithfulReconstructedDigraph G k S B ι hFaith).HasReachableRoots k ∧
      (∀ z : ReconstructedCarrier G k B,
        (faithfulReconstructedDigraph G k S B ι hFaith).roots k z =
        (Sum.inl : W → ReconstructedCarrier G k B) ''
          reconstructedSupport G k B z) := by
  have hRoot : ∀ r : W,
      (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k
        (.inl r) := by
    intro r
    exact faithful_reconstructed_root_outdegree_lt
      G k S B ι hFaith r
  have hNonroot : ∀ p : CanonicalNonroot G k B,
      ¬ (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k
        (.inr p) := by
    intro p
    exact faithful_reconstructed_nonroot_not_root
      G k S hBound hClosed hRootedS B ι hFaith p
  constructor
  · exact faithful_reconstructed_hasReachableRoots_of_support_paths
      G k S B ι hFaith hRoot hLift
  · intro z
    exact faithful_reconstructed_roots_eq_taggedSupport_of_conditions
      G k S B ι hFaith hRoot hNonroot hLift z

/-- Consequently the rooted k-orientation can be packaged with the
exact d-language expansion, whose functions are interpreted by
directed reachability and complete root fibres. -/
noncomputable def faithful_reconstructed_dStructure
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    Structure dLanguage (ReconstructedCarrier G k B) :=
  dStructure (faithfulReconstructedDigraph G k S B ι hFaith) k

/-- The d-expansion's unary function is *definitionally* the
directed reachable-vertex set; no arbitrary unary function is added. -/
@[simp] theorem faithful_reconstructed_dStructure_successors
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (xs : Fin 1 → ReconstructedCarrier G k B) :
    (faithful_reconstructed_dStructure G k S B ι hFaith).func
      DFunctionSymbol.successor xs =
      (faithfulReconstructedDigraph G k S B ι hFaith).successors
        (xs 0) := rfl

end AllThoseEPPA.Applications.KOrientations
