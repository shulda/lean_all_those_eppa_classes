import AllThoseEPPA.Applications.KOrientations.ReconstructionNestedNeighbourRigidity
import AllThoseEPPA.Applications.KOrientations.ReconstructedDigraph
import Mathlib.Data.Fintype.Card

/-!
# The outdegree bound at reconstructed non-root vertices

An outgoing neighbour of a canonical non-root p=(x,W) has a unique
template target in the original graph G:
* a B₁-root a points back to its matched template root r;
* a canonical non-root q points to its template centre q.center.

The two cases never collide because template roots and template
non-roots are disjoint. Injectivity on non-root targets follows from
nested-support rigidity, while injectivity on root targets follows
from the already certified uniqueness of root matching.

Thus the *entire* outgoing neighbourhood injects into the actual
outneighbourhood of x in G, proving outdegree <= k at every
reconstructed non-root. No unjustified fibre counting is used.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Assign to any outgoing reconstructed neighbour of (x,W)
its corresponding original G-outneighbour of x. -/
noncomputable def reconstructedNonrootNeighbourProjection
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (p : CanonicalNonroot G k B) :
    {z : ReconstructedCarrier G k B //
      ReconstructedEdge G k B (.inr p) z} →
      G.outNeighbors p.center := by
  classical
  intro z
  obtain ⟨z, hz⟩ := z
  cases z with
  | inl a =>
      change ∃ r : V, G.edge p.center r ∧
        RootMatches G k B p r a at hz
      exact ⟨Classical.choose hz,
        (G.mem_outNeighbors p.center (Classical.choose hz)).2
          (Classical.choose_spec hz).1⟩
  | inr q =>
      exact ⟨q.center,
        (G.mem_outNeighbors p.center q.center).2 hz.1⟩

/-- The template neighbour projection is injective on the complete
outgoing neighbourhood of a reconstructed non-root. -/
theorem reconstructedNonrootNeighbourProjection_injective
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B) :
    Function.Injective (reconstructedNonrootNeighbourProjection G k B p) := by
  classical
  intro z t heq
  obtain ⟨z, hz⟩ := z
  obtain ⟨t, ht⟩ := t
  apply Subtype.ext
  cases z with
  | inl a =>
      change ∃ r : V, G.edge p.center r ∧
        RootMatches G k B p r a at hz
      cases t with
      | inl b =>
          change ∃ r : V, G.edge p.center r ∧
            RootMatches G k B p r b at ht
          have hr : Classical.choose hz = Classical.choose ht := by
            have hv := congrArg Subtype.val heq
            change Classical.choose hz = Classical.choose ht at hv
            exact hv
          have hA : RootMatches G k B p (Classical.choose hz) a :=
            (Classical.choose_spec hz).2
          have hB : RootMatches G k B p (Classical.choose hz) b := by
            rw [hr]
            exact (Classical.choose_spec ht).2
          have hab : a = b :=
            RootMatches.right_unique p S ι hFaith hA hB
          exact congrArg Sum.inl hab
      | inr q =>
          have hcentre : Classical.choose hz = q.center := by
            have hv := congrArg Subtype.val heq
            change Classical.choose hz = q.center at hv
            exact hv
          have hroot : G.IsRoot k (Classical.choose hz) :=
            (RootMatches.root_mem p (Classical.choose_spec hz).2).1
          have hrootq : G.IsRoot k q.center := by
            rw [← hcentre]
            exact hroot
          exact False.elim (q.center_nonroot hrootq)
  | inr q =>
      cases t with
      | inl b =>
          change ∃ r : V, G.edge p.center r ∧
            RootMatches G k B p r b at ht
          have hcentre : q.center = Classical.choose ht := by
            have hv := congrArg Subtype.val heq
            change q.center = Classical.choose ht at hv
            exact hv
          have hroot : G.IsRoot k (Classical.choose ht) :=
            (RootMatches.root_mem p (Classical.choose_spec ht).2).1
          have hrootq : G.IsRoot k q.center := by
            rw [hcentre]
            exact hroot
          exact False.elim (q.center_nonroot hrootq)
      | inr t =>
          have hcentre : q.center = t.center := by
            have hv := congrArg Subtype.val heq
            change q.center = t.center at hv
            exact hv
          have hqt : q = t :=
            reconstructed_nonroot_neighbour_unique_of_center
              G k S B ι hFaith p q t hz ht hcentre
          exact congrArg Sum.inr hqt

/-- The complete outgoing neighbourhood of every reconstructed
non-root injects into the original outneighbourhood of its
template centre, so it has cardinality at most k. -/
theorem faithful_reconstructed_nonroot_outdegree_le
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B) :
    ((faithfulReconstructedDigraph G k S B ι hFaith).outNeighbors
      (.inr p)).card ≤ k := by
  classical
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  letI : Fintype (ReconstructedCarrier G k B) := Fintype.ofFinite _
  let N := {z : ReconstructedCarrier G k B //
    ReconstructedEdge G k B (.inr p) z}
  have hBoundCard :
      Fintype.card N ≤ (G.outNeighbors p.center).card := by
    have hi := Fintype.card_le_of_injective
      (reconstructedNonrootNeighbourProjection G k B p)
      (reconstructedNonrootNeighbourProjection_injective
        G k S B ι hFaith p)
    simpa only [Fintype.card_coe] using hi
  let e : N ≃ H.outNeighbors (.inr p) :=
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
  have hCardEq :
      (H.outNeighbors (.inr p)).card = Fintype.card N := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_coe] using h.symm
  calc
    (H.outNeighbors (.inr p)).card = Fintype.card N := hCardEq
    _ ≤ (G.outNeighbors p.center).card := hBoundCard
    _ ≤ k := hBound p.center

end AllThoseEPPA.Applications.KOrientations
