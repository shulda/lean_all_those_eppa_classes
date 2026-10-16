import AllThoseEPPA.Applications.KOrientations.ReconstructedDigraph
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdgeAction

/-!
# Actual reconstructed automorphisms preserve directed reachability

The canonical action induced by any second-stage automorphism has
already been proved to preserve and reflect each of the four
reconstructed edge clauses. Consequently it transports *entire*
oriented paths. This is the transport needed to turn a path in a
localized source copy into a path between the original reconstructed
vertices by applying the inverse automorphism.

No statements about k-degree, root status, or d-closure membership
are required for this graph-theoretic result.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A second-stage automorphism transports each path in the
reconstructed graph to a path between the transformed vertices. -/
theorem faithful_reconstructed_reaches_map
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {x y : ReconstructedCarrier G k B}
    (h : (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      x y) :
    (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      (reconstructedVertexPerm G k B f x)
      (reconstructedVertexPerm G k B f y) := by
  induction h with
  | refl x =>
      exact Digraph.Reaches.refl _
  | step hedge _ ih =>
      exact Digraph.Reaches.step
        (reconstructedEdge_map G k B f hedge) ih

/-- The transformation of paths is reversible because the canonical
reconstructed vertex action is an actual permutation. -/
theorem faithful_reconstructed_reaches_iff_map
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (x y : ReconstructedCarrier G k B) :
    (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      x y ↔
    (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      (reconstructedVertexPerm G k B f x)
      (reconstructedVertexPerm G k B f y) := by
  constructor
  · exact faithful_reconstructed_reaches_map G k S B ι hFaith f
  · intro h
    have hback :=
      faithful_reconstructed_reaches_map G k S B ι hFaith f.symm h
    have hinv (z : ReconstructedCarrier G k B) :
        reconstructedVertexPerm G k B f.symm
          (reconstructedVertexPerm G k B f z) = z := by
      cases z with
      | inl w =>
          change Sum.inl (f.symm (f w)) = Sum.inl w
          rw [Structure.Automorphism.symm_apply_apply]
      | inr p =>
          change Sum.inr
            (CanonicalNonroot.map f.symm (CanonicalNonroot.map f p)) =
              Sum.inr p
          rw [CanonicalNonroot.map_symm_apply]
    rw [hinv x, hinv y] at hback
    exact hback

end AllThoseEPPA.Applications.KOrientations
