import AllThoseEPPA.Applications.KOrientations.ReconstructionRootedDResult
import AllThoseEPPA.Applications.KOrientations.ClosedSubstructures
import AllThoseEPPA.Applications.KOrientations.SecondStageExactUnaryClosure

/-!
# Exact root traces of reconstructed closed d-substructures

The reconstructed root sort is the entire B₁ carrier, and each
reconstructed vertex has exact reachable-root set equal to its
intrinsic support, tagged into this root sort.

For every genuinely d-closed subset D of the reconstruction:
(1) the root trace D ∩ B₁ is closed under the genuine unary function
of the auxiliary B₁ structure, and
(2) D is determined exactly by which root-sort vertices it contains:
    z ∈ D ↔ support(z) ⊆ D ∩ B₁.

These facts are the first structural reduction needed to transfer
irreducibility from the reconstructed d-structure to the auxiliary
root structure. No faithfulness conclusion is assumed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The trace of a reconstructed vertex set on the B₁ root sort. -/
def reconstructedRootTrace
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (D : Set (ReconstructedCarrier G k B)) : Set W :=
  {w | (Sum.inl w : ReconstructedCarrier G k B) ∈ D}

/-- All reconstructed vertices intrinsically supported by a chosen
subset of auxiliary root vertices. -/
def reconstructedSupportedPiece
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (U : Set W) : Set (ReconstructedCarrier G k B) :=
  {z | reconstructedSupport G k B z ⊆ U}

/-- A closed d-substructure has a genuinely closed root trace in B₁,
not just a set-theoretic intersection with the tagged root sort. -/
theorem faithful_reconstructed_rootTrace_isClosed
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
    B.IsClosed (reconstructedRootTrace G k B D) := by
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  have hRootSets :
      ∀ z : ReconstructedCarrier G k B,
        H.roots k z =
          (Sum.inl : W → ReconstructedCarrier G k B) ''
            reconstructedSupport G k B z :=
    (faithful_reconstructed_exact_roots_and_rooted
      G k S hBound hClosed hRooted B ι hFaith).2
  have hDGraph : H.IsDClosed k D :=
    (dStructure_isClosed_iff H k D).mp hD
  intro n F xs hxs y hy
  cases F with
  | successor =>
      have hySupport :
          y ∈ reconstructedSupport G k B (.inl (xs 0)) := by
        change y ∈ B.closureAtSet (xs 0)
        rw [faithful_auxiliary_closureAt_eq_successors
          G k S B ι hFaith (xs 0)]
        exact hy
      have hyRoot :
          (Sum.inl y : ReconstructedCarrier G k B) ∈
            H.roots k (.inl (xs 0)) := by
        rw [hRootSets (.inl (xs 0))]
        exact ⟨y, hySupport, rfl⟩
      have hxD :
          (Sum.inl (xs 0) : ReconstructedCarrier G k B) ∈ D :=
        hxs 0
      exact hDGraph.1 _ _ hxD hyRoot.2

/-- Membership in every closed reconstructed d-substructure is
equivalent to containment of the entire intrinsic root support in
its auxiliary root trace. -/
theorem faithful_reconstructed_mem_closed_iff_support_subset_rootTrace
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
    (z : ReconstructedCarrier G k B) :
    z ∈ D ↔ reconstructedSupport G k B z ⊆
      reconstructedRootTrace G k B D := by
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  have hData := faithful_reconstructed_exact_roots_and_rooted
    G k S hBound hClosed hRooted B ι hFaith
  have hSat :
      ∀ z : ReconstructedCarrier G k B,
        z ∈ D ↔ H.roots k z ⊆ D :=
    (H.isDClosed_iff_rootSaturated k hData.1 D).mp
      ((dStructure_isClosed_iff H k D).mp hD)
  constructor
  · intro hz w hw
    have hRootMem :
        (Sum.inl w : ReconstructedCarrier G k B) ∈ H.roots k z := by
      rw [hData.2 z]
      exact ⟨w, hw, rfl⟩
    exact (hSat z).mp hz hRootMem
  · intro hz
    apply (hSat z).mpr
    intro r hr
    rw [hData.2 z] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    exact hz hw

/-- Equivalently, the *entire closed d-carrier* is exactly the
root-supported piece over its B₁-root trace. -/
theorem faithful_reconstructed_closed_eq_supportedPiece
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
    D = reconstructedSupportedPiece G k B
      (reconstructedRootTrace G k B D) := by
  ext z
  exact faithful_reconstructed_mem_closed_iff_support_subset_rootTrace
    G k S hBound hClosed hRooted B ι hFaith D hD z

end AllThoseEPPA.Applications.KOrientations
