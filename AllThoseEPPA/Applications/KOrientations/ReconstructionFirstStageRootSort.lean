import AllThoseEPPA.Applications.KOrientations.EmbeddedSuccessorSourceRooted
import AllThoseEPPA.Applications.KOrientations.ReconstructionExactDegrees

/-!
# Exact reconstructed root sort for the genuine first-stage source

Our second-stage exact-degree theorem only assumes a rooted and
successor-closed source S inside B₀; it never assumes B₀ itself is
rooted. The exact successor embedding A₀ → B₀ supplies exactly those
hypotheses for S=range(ι₀), because the original input A is rooted.

This result packages the derivation for downstream class-membership
proofs, avoiding extra unjustified hypotheses when instantiating
the reconstructed d-structure in the final coherent EPPA theorem.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- When the root-only auxiliary second-stage source is the root
trace of an exact first-stage embedding of a rooted input, the
root set of the reconstructed graph is precisely its B₁ sort. -/
theorem faithful_reconstructed_isRoot_iff_from_firstStage
    {U : Type u} {V : Type v} {W : Type w}
    [Fintype U] [Fintype V] [Fintype W]
    (k : ℕ)
    (A : KOrientation U k) (hRooted : A.graph.HasReachableRoots k)
    (G : KOrientation V k)
    (ι₀ : Structure.Embedding successorAction
      (successorStructure A.graph) (successorStructure G.graph))
    (B₁ : Structure (auxiliaryLanguage G.graph k) W)
    (ι₁ : Structure.Embedding (auxiliaryAction G.graph k)
      (auxiliaryRootStructure G.graph k (Set.range ι₀.toFun)) B₁)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G.graph k) ι₁)
    (z : ReconstructedCarrier G.graph k B₁) :
    (faithfulReconstructedDigraph G.graph k (Set.range ι₀.toFun)
      B₁ ι₁ hFaith).IsRoot k z ↔
      ∃ r : W, z = Sum.inl r := by
  have hClosed :
      ∀ x y : V, x ∈ Set.range ι₀.toFun →
        G.graph.Reaches x y → y ∈ Set.range ι₀.toFun :=
    successorEmbedding_image_successorClosed A.graph G.graph ι₀
  have hRoots :
      ∀ x : V, x ∈ Set.range ι₀.toFun →
        (G.graph.roots k x).Nonempty :=
    successorEmbedding_image_rooted A.graph G.graph k hRooted ι₀
  exact faithful_reconstructed_isRoot_iff_isRootSort
    G.graph k (Set.range ι₀.toFun) G.bound hClosed hRoots
    B₁ ι₁ hFaith z

/-- Every reconstructed nonroot in the first-stage situation has
exactly k outgoing neighbours in the final directed graph. -/
theorem faithful_reconstructed_nonroot_degree_from_firstStage
    {U : Type u} {V : Type v} {W : Type w}
    [Fintype U] [Fintype V] [Fintype W]
    (k : ℕ)
    (A : KOrientation U k) (hRooted : A.graph.HasReachableRoots k)
    (G : KOrientation V k)
    (ι₀ : Structure.Embedding successorAction
      (successorStructure A.graph) (successorStructure G.graph))
    (B₁ : Structure (auxiliaryLanguage G.graph k) W)
    (ι₁ : Structure.Embedding (auxiliaryAction G.graph k)
      (auxiliaryRootStructure G.graph k (Set.range ι₀.toFun)) B₁)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G.graph k) ι₁)
    (p : CanonicalNonroot G.graph k B₁) :
    ((faithfulReconstructedDigraph G.graph k (Set.range ι₀.toFun)
      B₁ ι₁ hFaith).outNeighbors (.inr p)).card = k := by
  exact faithful_reconstructed_nonroot_outdegree_eq
    G.graph k (Set.range ι₀.toFun) G.bound
    (successorEmbedding_image_successorClosed A.graph G.graph ι₀)
    (successorEmbedding_image_rooted A.graph G.graph k hRooted ι₀)
    B₁ ι₁ hFaith p

end AllThoseEPPA.Applications.KOrientations
