import AllThoseEPPA.Applications.KOrientations.ReconstructionRootNeighbourInjective
import Mathlib.Data.Fintype.Card

/-!
# Every reconstructed B₁-root has outdegree strictly below k

The mixed root-neighbour projection, already proved injective,
sends the entire outgoing neighbourhood to the original
outneighbourhood of a root of the B₀ template. Thus its cardinality
is bounded by a cardinal strictly below k.

No separate case count or disjointness assumption is hidden:
the fibre injection distinguishes root from non-root template
images, and handles all E_P-coded neighbours.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

theorem faithful_reconstructed_root_outdegree_lt
    {V : Type u} [Fintype V] {W : Type v} [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : W) :
    ((faithfulReconstructedDigraph G k S B ι hFaith).outNeighbors
      (.inl a)).card < k := by
  classical
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  let anchor : AuxiliaryRootAnchor G k S B ι a :=
    Classical.choice (auxiliaryRootAnchor_exists G k S B ι hFaith a)
  let N := {z : ReconstructedCarrier G k B //
    ReconstructedEdge G k B (.inl a) z}
  have hLe : Fintype.card N ≤ (G.outNeighbors anchor.source.val).card := by
    have hi := Fintype.card_le_of_injective
      (reconstructedRootNeighbourProjection G k S B ι hFaith a anchor)
      (reconstructedRootNeighbourProjection_injective
        G k S B ι hFaith a anchor)
    simpa only [Fintype.card_coe] using hi
  let e : N ≃ H.outNeighbors (.inl a) :=
    { toFun := fun z =>
        ⟨z.val,(H.mem_outNeighbors (.inl a) z.val).2 z.property⟩
      invFun := fun z =>
        ⟨z.val,(H.mem_outNeighbors (.inl a) z.val).1 z.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        rfl
      right_inv := by
        intro z
        apply Subtype.ext
        rfl }
  have hCard : (H.outNeighbors (.inl a)).card = Fintype.card N := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_coe] using h.symm
  calc
    (H.outNeighbors (.inl a)).card = Fintype.card N := hCard
    _ ≤ (G.outNeighbors anchor.source.val).card := hLe
    _ < k := anchor.source.property.2

end AllThoseEPPA.Applications.KOrientations
