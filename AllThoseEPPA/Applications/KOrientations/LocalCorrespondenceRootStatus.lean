import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceReachability
import AllThoseEPPA.Applications.KOrientations.ReconstructionExactDegrees

/-!
# Root status is reflected by the local correspondence

The locally moved correspondence is already an injective induced graph
embedding and preserves directed paths. In the reconstructed rooted
source setting, it also preserves and reflects the degree-defined
root predicate.

For a B₁-root the correspondence lands by construction in the source
root sort. For a canonical nonroot, its image is the template centre
transported by a genuine graph automorphism, so remains a nonroot.
The exact reconstructed nonroot degree theorem is used here: the
mere bound `≤ k` would not suffice to identify root status.

This gives the root-predicate part of the future closed-piece d-language
isomorphism; surjectivity and function reflection remain separate.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Under the genuine successor-closed rooted source assumptions, the
local graph correspondence preserves *and reflects* the root predicate
of the final reconstructed k-orientation. -/
theorem localCorrespondence_isRoot_iff
    {V : Type u} [Fintype V] {W : Type v} [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hBound : G.HasOutdegreeAtMost k)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (z : LocalReconstructedCarrier G k S B ι f) :
    G.IsRoot k (localCorrespondence G k S B ι f z) ↔
      (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k z.val := by
  classical
  obtain ⟨z, hz⟩ := z
  cases z with
  | inl a =>
      have hTarget :
          G.IsRoot k (localCorrespondence G k S B ι f ⟨.inl a, hz⟩) := by
        change G.IsRoot k
          (Classical.choose (hz a (B.mem_closureAtSet a))).val
        exact (Classical.choose
          (hz a (B.mem_closureAtSet a))).property.2
      constructor
      · intro _
        exact faithful_reconstructed_root_outdegree_lt
          G k S B ι hFaith a
      · intro _
        exact hTarget
  | inr p =>
      have hTarget :
          ¬ G.IsRoot k
            ((ι.lang⁻¹ * f.lang : G.graphAut).1 p.center) := by
        intro hr
        exact p.center_nonroot
          ((G.graphAut_root_iff k
            (ι.lang⁻¹ * f.lang : G.graphAut) p.center).mp hr)
      have hSource :
          ¬ (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot
            k (.inr p) :=
        faithful_reconstructed_nonroot_not_root
          G k S hBound hClosed hRooted B ι hFaith p
      change G.IsRoot k
        ((ι.lang⁻¹ * f.lang : G.graphAut).1 p.center) ↔
        (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot
          k (.inr p)
      exact ⟨fun h => (hTarget h).elim, fun h => (hSource h).elim⟩

end AllThoseEPPA.Applications.KOrientations
