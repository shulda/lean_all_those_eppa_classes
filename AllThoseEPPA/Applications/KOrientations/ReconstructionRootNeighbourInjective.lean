import AllThoseEPPA.Applications.KOrientations.ReconstructionRootNeighbourProjection

/-!
# Injectivity of the full outgoing-root neighbourhood projection

The source of every outgoing edge from a B₁-root a can be projected
through one common anchor automorphism into the original root's
outneighbourhood. Injectivity splits into four tag cases:

* root/root: the anchor automorphism is injective;
* root/nonroot and nonroot/root: the original images have opposite
  root predicates;
* nonroot/nonroot: equal template centres and the common moved
  supports imply equality by CommonMoveRootRigidity.

The target of this theorem includes *all* B₁-root successors,
including those encoded by an incoming E_P relation.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

theorem reconstructedRootNeighbourProjection_injective
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
  obtain ⟨z,hz⟩ := z
  obtain ⟨t,ht⟩ := t
  apply Subtype.ext
  cases z with
  | inl b =>
      change B.rel AuxiliaryRel.edge ![a,b] at hz
      cases t with
      | inl c =>
          change B.rel AuxiliaryRel.edge ![a,c] at ht
          have hImage :
              (Classical.choose (anchor.move_rootEdge hFaith hz)).val =
              (Classical.choose (anchor.move_rootEdge hFaith ht)).val := by
            have hv := congrArg Subtype.val heq
            change
              (Classical.choose (anchor.move_rootEdge hFaith hz)).val =
              (Classical.choose (anchor.move_rootEdge hFaith ht)).val at hv
            exact hv
          have hTarget :
              Classical.choose (anchor.move_rootEdge hFaith hz) =
              Classical.choose (anchor.move_rootEdge hFaith ht) :=
            Subtype.ext hImage
          have hb :
              anchor.mover b =
                ι (Classical.choose (anchor.move_rootEdge hFaith hz)) :=
            (Classical.choose_spec (anchor.move_rootEdge hFaith hz)).1
          have hc :
              anchor.mover c =
                ι (Classical.choose (anchor.move_rootEdge hFaith ht)) :=
            (Classical.choose_spec (anchor.move_rootEdge hFaith ht)).1
          have hbc : b = c := by
            apply anchor.mover.toEquiv.injective
            calc
              anchor.mover b =
                  ι (Classical.choose (anchor.move_rootEdge hFaith hz)) := hb
              _ = ι (Classical.choose (anchor.move_rootEdge hFaith ht)) :=
                congrArg ι hTarget
              _ = anchor.mover c := hc.symm
          exact congrArg Sum.inl hbc
      | inr p =>
          have hImage :
              (Classical.choose (anchor.move_rootEdge hFaith hz)).val =
              anchor.templateMap.1 p.center := by
            have hv := congrArg Subtype.val heq
            change
              (Classical.choose (anchor.move_rootEdge hFaith hz)).val =
              anchor.templateMap.1 p.center at hv
            exact hv
          have hRoot :
              G.IsRoot k (anchor.templateMap.1 p.center) := by
            rw [← hImage]
            exact (Classical.choose (anchor.move_rootEdge hFaith hz)).property.2
          have hNot : ¬ G.IsRoot k (anchor.templateMap.1 p.center) := by
            intro hr
            exact p.center_nonroot
              ((G.graphAut_root_iff k anchor.templateMap p.center).mp hr)
          exact False.elim (hNot hRoot)
  | inr p =>
      change IncomingRealized G k B a p at hz
      cases t with
      | inl b =>
          change B.rel AuxiliaryRel.edge ![a,b] at ht
          have hImage :
              anchor.templateMap.1 p.center =
              (Classical.choose (anchor.move_rootEdge hFaith ht)).val := by
            have hv := congrArg Subtype.val heq
            change
              anchor.templateMap.1 p.center =
              (Classical.choose (anchor.move_rootEdge hFaith ht)).val at hv
            exact hv
          have hRoot :
              G.IsRoot k (anchor.templateMap.1 p.center) := by
            rw [hImage]
            exact (Classical.choose (anchor.move_rootEdge hFaith ht)).property.2
          have hNot : ¬ G.IsRoot k (anchor.templateMap.1 p.center) := by
            intro hr
            exact p.center_nonroot
              ((G.graphAut_root_iff k anchor.templateMap p.center).mp hr)
          exact False.elim (hNot hRoot)
      | inr q =>
          change IncomingRealized G k B a q at ht
          have hImage :
              anchor.templateMap.1 p.center =
                anchor.templateMap.1 q.center := by
            have hv := congrArg Subtype.val heq
            change anchor.templateMap.1 p.center =
              anchor.templateMap.1 q.center at hv
            exact hv
          have hCenter : p.center = q.center :=
            anchor.templateMap.1.injective hImage
          have hpSub : p.support ⊆ B.closureAtSet a :=
            faithful_incoming_support_subset_closure
              G k S B ι hFaith a p hz
          have hqSub : q.support ⊆ B.closureAtSet a :=
            faithful_incoming_support_subset_closure
              G k S B ι hFaith a q ht
          have hpMove :
              ∀ w ∈ p.support,
                ∃ y : RootsIn G k S, anchor.mover w = ι y := by
            intro w hw
            exact anchor.moves_closure w (hpSub hw)
          have hqMove :
              ∀ w ∈ q.support,
                ∃ y : RootsIn G k S, anchor.mover w = ι y := by
            intro w hw
            exact anchor.moves_closure w (hqSub hw)
          have hpq : p = q :=
            canonicalNonroot_eq_of_common_move
              G k S B ι anchor.mover p q hCenter hpMove hqMove
          exact congrArg Sum.inr hpq

end AllThoseEPPA.Applications.KOrientations
