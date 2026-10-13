import AllThoseEPPA.Applications.KOrientations.SecondStageRootIncomingAnchor
import AllThoseEPPA.Applications.KOrientations.CommonMoveRootRigidity
import AllThoseEPPA.Applications.KOrientations.ReconstructionNonrootOutdegree
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportMonotone
import Mathlib.Data.Fintype.Card

/-!
# Full reconstructed outdegree bound at root vertices

Fix a reconstructed root a ∈ B₁. Faithfulness supplies ONE
automorphism f transporting the whole singleton closure of a to the
distinguished root sort A₁. Root-to-root neighbours are mapped to the
source vertices t, with f(b)=ι(t), while root-to-nonroot neighbours
p=(x,W) map to the template centre g(x), where
g = ι.lang⁻¹ * f.lang.

A common move of all supports is crucial: it forces any two nonroot
neighbours with the same transported centre to have the same support.
This gives an injection from the entire outneighbourhood of a into
the outneighbourhood of the actual original root anchor.source.
Its degree is < k. Together with the already certified bound for
nonroots, this yields the full reconstructed k-orientation.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The template root corresponding to a B₁-root neighbour through a
fixed common source-move anchor. -/
private noncomputable def reconstructedRootTarget
    {V : Type u} [Fintype V] {W : Type v}
    {G : Digraph V} {k : ℕ} {S : Set V}
    {B : Structure (auxiliaryLanguage G k) W}
    {ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B}
    {a b : W}
    (anchor : AuxiliaryRootAnchor G k S B ι a)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (hEdge : B.rel AuxiliaryRel.edge ![a,b]) :
    RootsIn G k S :=
  Classical.choose (anchor.move_rootEdge hFaith hEdge)

/-- The chosen target is tracked by the same B₁ automorphism. -/
private theorem reconstructedRootTarget_eq
    {V : Type u} [Fintype V] {W : Type v}
    {G : Digraph V} {k : ℕ} {S : Set V}
    {B : Structure (auxiliaryLanguage G k) W}
    {ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B}
    {a b : W}
    (anchor : AuxiliaryRootAnchor G k S B ι a)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (hEdge : B.rel AuxiliaryRel.edge ![a,b]) :
    anchor.mover b = ι (reconstructedRootTarget anchor hFaith hEdge) :=
  (Classical.choose_spec (anchor.move_rootEdge hFaith hEdge)).1

/-- The selected template root is an outgoing neighbour of the
source root of the anchor. -/
private theorem reconstructedRootTarget_edge
    {V : Type u} [Fintype V] {W : Type v}
    {G : Digraph V} {k : ℕ} {S : Set V}
    {B : Structure (auxiliaryLanguage G k) W}
    {ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B}
    {a b : W}
    (anchor : AuxiliaryRootAnchor G k S B ι a)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (hEdge : B.rel AuxiliaryRel.edge ![a,b]) :
    G.edge anchor.source.val (reconstructedRootTarget anchor hFaith hEdge).val :=
  (Classical.choose_spec (anchor.move_rootEdge hFaith hEdge)).2

/-- Inject every outgoing reconstructed neighbour of a B₁ root into
the outneighbours of the common source root in the template graph. -/
private noncomputable def reconstructedRootNeighbourProjection
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : W)
    (anchor : AuxiliaryRootAnchor G k S B ι a) :
    {z : ReconstructedCarrier G k B //
      ReconstructedEdge G k B (.inl a) z} →
    G.outNeighbors anchor.source.val := by
  classical
  intro z
  obtain ⟨z, hz⟩ := z
  cases z with
  | inl b =>
      let t := reconstructedRootTarget anchor hFaith hz
      exact ⟨t.val,
        (G.mem_outNeighbors anchor.source.val t.val).2
          (reconstructedRootTarget_edge anchor hFaith hz)⟩
  | inr p =>
      have hSupport : p.support ⊆ B.closureAtSet a :=
        faithful_reconstructedEdge_support_antitone G k S B ι hFaith hz
      exact ⟨anchor.templateMap.1 p.center,
        (G.mem_outNeighbors anchor.source.val
          (anchor.templateMap.1 p.center)).2
          (anchor.move_incoming p hz hSupport)⟩

/-- The single source-moving automorphism prevents collisions among
outgoing neighbours, both within and between the two vertex sorts. -/
private theorem reconstructedRootNeighbourProjection_injective
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : W)
    (anchor : AuxiliaryRootAnchor G k S B ι a) :
    Function.Injective
      (reconstructedRootNeighbourProjection G k S B ι hFaith a anchor) := by
  classical
  intro z t heq
  obtain ⟨z, hz⟩ := z
  obtain ⟨t, ht⟩ := t
  apply Subtype.ext
  cases z with
  | inl b =>
      cases t with
      | inl c =>
          have hv := congrArg Subtype.val heq
          change
            (reconstructedRootTarget anchor hFaith hz).val =
            (reconstructedRootTarget anchor hFaith ht).val at hv
          have hroot :
              reconstructedRootTarget anchor hFaith hz =
              reconstructedRootTarget anchor hFaith ht :=
            Subtype.ext hv
          have hf : anchor.mover b = anchor.mover c := by
            calc
              anchor.mover b =
                  ι (reconstructedRootTarget anchor hFaith hz) :=
                reconstructedRootTarget_eq anchor hFaith hz
              _ = ι (reconstructedRootTarget anchor hFaith ht) :=
                congrArg ι hroot
              _ = anchor.mover c :=
                (reconstructedRootTarget_eq anchor hFaith ht).symm
          exact congrArg Sum.inl (anchor.mover.toEquiv.injective hf)
      | inr q =>
          have hv := congrArg Subtype.val heq
          change (reconstructedRootTarget anchor hFaith hz).val =
            anchor.templateMap.1 q.center at hv
          have hroot : G.IsRoot k (anchor.templateMap.1 q.center) := by
            rw [← hv]
            exact (reconstructedRootTarget anchor hFaith hz).property.2
          have hq : G.IsRoot k q.center :=
            (G.graphAut_root_iff k anchor.templateMap q.center).mp hroot
          exact False.elim (q.center_nonroot hq)
  | inr p =>
      cases t with
      | inl c =>
          have hv := congrArg Subtype.val heq
          change anchor.templateMap.1 p.center =
            (reconstructedRootTarget anchor hFaith ht).val at hv
          have hroot : G.IsRoot k (anchor.templateMap.1 p.center) := by
            rw [hv]
            exact (reconstructedRootTarget anchor hFaith ht).property.2
          have hp : G.IsRoot k p.center :=
            (G.graphAut_root_iff k anchor.templateMap p.center).mp hroot
          exact False.elim (p.center_nonroot hp)
      | inr q =>
          have hv := congrArg Subtype.val heq
          change anchor.templateMap.1 p.center =
            anchor.templateMap.1 q.center at hv
          have hcentre : p.center = q.center :=
            anchor.templateMap.1.injective hv
          have hpMove :
              ∀ w ∈ p.support, ∃ t : RootsIn G k S,
                anchor.mover w = ι t := by
            intro w hw
            apply anchor.moves_closure
            exact (faithful_reconstructedEdge_support_antitone
              G k S B ι hFaith hz) hw
          have hqMove :
              ∀ w ∈ q.support, ∃ t : RootsIn G k S,
                anchor.mover w = ι t := by
            intro w hw
            apply anchor.moves_closure
            exact (faithful_reconstructedEdge_support_antitone
              G k S B ι hFaith ht) hw
          have hpq : p = q :=
            canonicalNonroot_eq_of_common_move
              G k S B ι anchor.mover p q hcentre hpMove hqMove
          exact congrArg Sum.inr hpq

/-- Every reconstructed B₁ root has strictly less than k outgoing
neighbours, as its entire neighbourhood injects into the original
template root's outgoing neighbourhood. -/
theorem faithful_reconstructed_root_outdegree_lt
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
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
  obtain ⟨anchor⟩ :=
    auxiliaryRootAnchor_exists G k S B ι hFaith a
  let H := faithfulReconstructedDigraph G k S B ι hFaith
  let N := {z : ReconstructedCarrier G k B //
    ReconstructedEdge G k B (.inl a) z}
  have hBoundCard :
      Fintype.card N ≤ (G.outNeighbors anchor.source.val).card := by
    have hi := Fintype.card_le_of_injective
      (reconstructedRootNeighbourProjection G k S B ι hFaith a anchor)
      (reconstructedRootNeighbourProjection_injective
        G k S B ι hFaith a anchor)
    simpa only [Fintype.card_coe] using hi
  let e : N ≃ H.outNeighbors (.inl a) :=
    { toFun := fun z =>
        ⟨z.val, (H.mem_outNeighbors (.inl a) z.val).2 z.property⟩
      invFun := fun z =>
        ⟨z.val, (H.mem_outNeighbors (.inl a) z.val).1 z.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        rfl
      right_inv := by
        intro z
        apply Subtype.ext
        rfl }
  have hCardEq :
      (H.outNeighbors (.inl a)).card = Fintype.card N := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_coe] using h.symm
  calc
    (H.outNeighbors (.inl a)).card = Fintype.card N := hCardEq
    _ ≤ (G.outNeighbors anchor.source.val).card := hBoundCard
    _ < k := anchor.source.property.2

/-- Every vertex of the reconstructed digraph has outdegree at most
k. Roots in B₁ actually have strict outdegree < k, while nonroots
satisfy the weak bound by the separate projection theorem. -/
theorem faithful_reconstructed_hasOutdegreeAtMost
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    (faithfulReconstructedDigraph G k S B ι hFaith).HasOutdegreeAtMost k := by
  intro z
  cases z with
  | inl a =>
      exact Nat.le_of_lt
        (faithful_reconstructed_root_outdegree_lt
          G k S B ι hFaith a)
  | inr p =>
      exact faithful_reconstructed_nonroot_outdegree_le
        G k S hBound B ι hFaith p

/-- The reconstructed graph really is a finite k-orientation, not
just an asymmetric directed graph. -/
noncomputable def faithfulReconstructedKOrientation
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    KOrientation (ReconstructedCarrier G k B) k where
  graph := faithfulReconstructedDigraph G k S B ι hFaith
  bound := faithful_reconstructed_hasOutdegreeAtMost
    G k S hBound B ι hFaith

end AllThoseEPPA.Applications.KOrientations
