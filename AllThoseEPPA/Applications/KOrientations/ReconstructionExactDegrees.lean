import AllThoseEPPA.Applications.KOrientations.ReconstructionNonrootSurjectivity
import AllThoseEPPA.Applications.KOrientations.ReconstructionRootOutdegree
import Mathlib.Data.Fintype.Card

/-!
# Exactly k outgoing neighbours for reconstructed nonroots

Under the genuine source assumptions (successor-closed S and every
element of S reaching a root), the earlier nonroot neighbourhood
projection is both injective and surjective. It identifies the whole
outneighbourhood of a canonical nonroot p=(x,W) with that of x in B₀.

Since p.center is a template nonroot, the original bounded-k graph
has exactly k outgoing neighbours there, and thus so does p.
Together with the strict root bound in ReconstructionRootOutdegree,
this identifies precisely the actual root sort of the reconstructed
graph. No ambient rootedness assumption on B₀ is used.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A genuine outdegree equality for canonical reconstructed nonroots,
conditional exactly on the rooted successor-closed source properties. -/
theorem faithful_reconstructed_nonroot_outdegree_eq
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (hRootedS : ∀ x : V, x ∈ S → (G.roots k x).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B) :
    ((faithfulReconstructedDigraph G k S B ι hFaith).outNeighbors
      (.inr p)).card = k := by
  classical
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  let N := {z : ReconstructedCarrier G k B //
    ReconstructedEdge G k B (.inr p) z}
  let projection := reconstructedNonrootNeighbourProjection G k B p
  have hBij : Function.Bijective projection :=
    ⟨reconstructedNonrootNeighbourProjection_injective
      G k S B ι hFaith p,
     reconstructedNonrootNeighbourProjection_surjective
      G k S hClosed hRootedS B ι hFaith p⟩
  let e : N ≃ G.outNeighbors p.center :=
    Equiv.ofBijective projection hBij
  have hProjectionCard :
      Fintype.card N = (G.outNeighbors p.center).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  let d : N ≃ H.outNeighbors (.inr p) :=
    { toFun := fun z =>
        ⟨z.val, (H.mem_outNeighbors (.inr p) z.val).2 z.property⟩
      invFun := fun z =>
        ⟨z.val, (H.mem_outNeighbors (.inr p) z.val).1 z.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        rfl
      right_inv := by
        intro z
        apply Subtype.ext
        rfl }
  have hNeighbourCard :
      (H.outNeighbors (.inr p)).card = Fintype.card N := by
    have h := Fintype.card_congr d
    simpa only [Fintype.card_coe] using h.symm
  calc
    (H.outNeighbors (.inr p)).card = Fintype.card N := hNeighbourCard
    _ = (G.outNeighbors p.center).card := hProjectionCard
    _ = k := G.degree_eq_of_not_root k hBound p.center_nonroot

/-- Hence no reconstructed canonical nonroot can accidentally be
classified as a root by its outgoing degree. -/
theorem faithful_reconstructed_nonroot_not_root
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (hRootedS : ∀ x : V, x ∈ S → (G.roots k x).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B) :
    ¬ (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot
      k (.inr p) := by
  intro hRoot
  have hDegree :=
    faithful_reconstructed_nonroot_outdegree_eq
      G k S hBound hClosed hRootedS B ι hFaith p
  change ((faithfulReconstructedDigraph G k S B ι hFaith).outNeighbors
    (.inr p)).card < k at hRoot
  rw [hDegree] at hRoot
  exact (Nat.lt_irrefl k) hRoot

/-- Root vertices of the final reconstructed k-orientation are
*exactly* those belonging to B₁, once the source is rooted and
successor-closed. -/
theorem faithful_reconstructed_isRoot_iff_isRootSort
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ x y : V, x ∈ S → G.Reaches x y → y ∈ S)
    (hRootedS : ∀ x : V, x ∈ S → (G.roots k x).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (z : ReconstructedCarrier G k B) :
    (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k z ↔
      ∃ r : W, z = Sum.inl r := by
  cases z with
  | inl a =>
      constructor
      · intro _
        exact ⟨a, rfl⟩
      · intro _
        exact faithful_reconstructed_root_outdegree_lt
          G k S B ι hFaith a
  | inr p =>
      constructor
      · intro h
        exact (faithful_reconstructed_nonroot_not_root
          G k S hBound hClosed hRootedS B ι hFaith p h).elim
      · rintro ⟨r, h⟩
        cases h

end AllThoseEPPA.Applications.KOrientations
