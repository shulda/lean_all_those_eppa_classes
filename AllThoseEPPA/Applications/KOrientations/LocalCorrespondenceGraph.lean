import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceInjective
import AllThoseEPPA.Applications.KOrientations.LocalRootEdgeTransfer
import AllThoseEPPA.Applications.KOrientations.LocalRootIncomingEdgeTransfer
import AllThoseEPPA.Applications.KOrientations.LocalNonrootRootEdgeTransfer
import AllThoseEPPA.Applications.KOrientations.LocalNonrootEdgeTransfer

/-!
# Claim P2: the local correspondence is an induced graph embedding

The local map c_f is defined only on reconstructed vertices whose
entire supports are moved into the old root sort by the *same*
automorphism f of B₁. The four source-transport lemmas prove that
it preserves AND REFLECTS every kind of directed edge.

Together with the checked Claim P1 (injectivity), this gives
an actual induced subgraph embedding of the locally moved domain
into the first-stage template graph B₀. It does not yet assert
surjectivity onto a closed piece or preservation of d-functions.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

theorem localCorrespondence_edge_iff
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (x y : LocalReconstructedCarrier G k S B ι f) :
    ReconstructedEdge G k B x.val y.val ↔
      G.edge
        (localCorrespondence G k S B ι f x)
        (localCorrespondence G k S B ι f y) := by
  classical
  obtain ⟨x,hx⟩ := x
  obtain ⟨y,hy⟩ := y
  cases x with
  | inl a =>
      let ra : RootsIn G k S :=
        Classical.choose (hx a (B.mem_closureAtSet a))
      have ha : f a = ι ra :=
        Classical.choose_spec (hx a (B.mem_closureAtSet a))
      cases y with
      | inl b =>
          let rb : RootsIn G k S :=
            Classical.choose (hy b (B.mem_closureAtSet b))
          have hb : f b = ι rb :=
            Classical.choose_spec (hy b (B.mem_closureAtSet b))
          change B.rel AuxiliaryRel.edge ![a,b] ↔
            G.edge ra.val rb.val
          exact faithful_auxiliary_edge_iff_under_move
            G k S B ι f a b ra rb ha hb
      | inr q =>
          change IncomingRealized G k B a q ↔
            G.edge ra.val
              ((ι.lang⁻¹*f.lang : G.graphAut).1 q.center)
          exact local_root_nonroot_edge_iff
            G k S B ι f a ra ha q hy
  | inr p =>
      cases y with
      | inl b =>
          let rb : RootsIn G k S :=
            Classical.choose (hy b (B.mem_closureAtSet b))
          have hb : f b = ι rb :=
            Classical.choose_spec (hy b (B.mem_closureAtSet b))
          change ReconstructedEdge G k B (.inr p) (.inl b) ↔
            G.edge
              ((ι.lang⁻¹*f.lang : G.graphAut).1 p.center) rb.val
          exact local_nonroot_root_edge_iff
            G k S B ι f p hx b rb hb
      | inr q =>
          change ReconstructedEdge G k B (.inr p) (.inr q) ↔
            G.edge
              ((ι.lang⁻¹*f.lang : G.graphAut).1 p.center)
              ((ι.lang⁻¹*f.lang : G.graphAut).1 q.center)
          exact local_nonroot_nonroot_edge_iff
            G k S B ι f p q hx hy

/-- The locally moved part of the reconstructed graph embeds as
an **induced** subgraph of B₀ under c_f. -/
theorem localCorrespondence_graphEmbedding
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Function.Injective (localCorrespondence G k S B ι f) ∧
    ∀ (x y : LocalReconstructedCarrier G k S B ι f),
      ReconstructedEdge G k B x.val y.val ↔
        G.edge (localCorrespondence G k S B ι f x)
               (localCorrespondence G k S B ι f y) := by
  exact ⟨localCorrespondence_injective G k S B ι f,
    localCorrespondence_edge_iff G k S B ι f⟩

end AllThoseEPPA.Applications.KOrientations
