import AllThoseEPPA.Applications.KOrientations.Graph

/-!
# Directed paths are intrinsic to successor-closed induced subgraphs

Let S,T be subsets of directed graphs, each closed under outgoing
edges. An induced graph isomorphism S ≃ T then preserves and reflects
all directed paths in the ambient graphs, not only paths in a
separately defined induced graph. The point is that all intermediate
vertices of each path stay within the relevant subset.

This is a language-independent part of the future theorem that a
graph isomorphism between d-closed pieces automatically preserves
the entire d-language. No rootedness or EPPA hypotheses are needed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Any edge-induced bijection between successor-closed vertex subsets
preserves and reflects ambient directed reachability. -/
theorem reaches_iff_of_equiv_on_successor_closed
    {V : Type u} {W : Type v}
    (G : Digraph V) (H : Digraph W)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    (x y : S) :
    G.Reaches x.val y.val ↔
      H.Reaches (e x).val (e y).val := by
  have hForward :
      ∀ {a b : V}, G.Reaches a b →
        ∀ ha : a ∈ S,
          ∃ hb : b ∈ S,
            H.Reaches (e ⟨a, ha⟩).val (e ⟨b, hb⟩).val := by
    intro a b hPath
    induction hPath with
    | refl a =>
        intro ha
        exact ⟨ha, H.reaches_refl _⟩
    | @step a b c hab hbc ih =>
        intro ha
        have hb : b ∈ S := hS a b ha hab
        obtain ⟨hc, hRest⟩ := ih hb
        refine ⟨hc, H.reaches_trans ?_ hRest⟩
        exact H.reaches_of_edge
          ((hEdge ⟨a, ha⟩ ⟨b, hb⟩).mp hab)
  have hEdgeBack :
      ∀ p q : T,
        H.edge p.val q.val ↔
          G.edge (e.symm p).val (e.symm q).val := by
    intro p q
    have h := hEdge (e.symm p) (e.symm q)
    simpa only [e.apply_symm_apply] using h.symm
  have hBackward :
      ∀ {a b : W}, H.Reaches a b →
        ∀ ha : a ∈ T,
          ∃ hb : b ∈ T,
            G.Reaches (e.symm ⟨a, ha⟩).val
              (e.symm ⟨b, hb⟩).val := by
    intro a b hPath
    induction hPath with
    | refl a =>
        intro ha
        exact ⟨ha, G.reaches_refl _⟩
    | @step a b c hab hbc ih =>
        intro ha
        have hb : b ∈ T := hT a b ha hab
        obtain ⟨hc, hRest⟩ := ih hb
        refine ⟨hc, G.reaches_trans ?_ hRest⟩
        exact G.reaches_of_edge
          ((hEdgeBack ⟨a, ha⟩ ⟨b, hb⟩).mp hab)
  constructor
  · intro h
    obtain ⟨_, hPath⟩ := hForward h x.property
    exact hPath
  · intro h
    obtain ⟨_, hPath⟩ := hBackward h (e x).property
    simpa only [e.symm_apply_apply] using hPath

end AllThoseEPPA.Applications.KOrientations
