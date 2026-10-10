import AllThoseEPPA.TreeLikeTowerCycleFreeAncestor
import AllThoseEPPA.TreeLikeCutsRealization
import AllThoseEPPA.TreeLikeFaithfulEmbeddingBridge
import AllThoseEPPA.TreeLikeInducedEmbeddings
import AllThoseEPPA.TreeLikeInducedCycles

/-!
# Realize the actual cycle-free sparsening ancestor in a full-A tree

The already proved `lem:cuts` says that a finite
cycle-free structure whose irreducible substructures
embed into A itself embeds *exactly* into a tree
amalgamation of full copies of A.

The previous bounded-rank descent found a genuine
closed projected ancestor of a chosen small closed
subset in the actual finite sparsening tower, and
certified that it has no long induced E-cycles.

This file composes **these two checked results**:
each cycle-free closed subset in a faithful sparsening
stage embeds into a full-A tree; in particular the
ancestor found by the real bounded-rank descent does.

This is not yet the full `thm:maintree`: the remaining
substantive task is to transport the *original top
substructure* to this ancestor by composing the
homomorphism-embeddings in its certified backwards
projection chain, and finally take the E-reduct.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)} [Finite α]

namespace ClosedStageSubset

/-- A cycle-free closed substructure of an actual finite,
irreducible-faithful Γ-EPPA stage embeds exactly into
a tree amalgamation of **full** copies of A.

No extra graph symmetry or looplessness hypothesis is
imposed: both are automatic from faithfulness and
the fact that E is Γ-fixed and complete on A. -/
theorem embeds_fullATree_of_noBadCycles
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (T : ClosedStageSubset act A s)
    (hNo : ∀ c : Structure.BadCycleSequence
      (s.model.induce T.support T.closed) E, False) :
    ∃ (W : Type (max u v)) (H : Structure L W),
      TreeAmalgamation act A H ∧
        Nonempty (Structure.Embedding act
          (s.model.induce T.support T.closed) H) := by
  letI : Finite s.Carrier := s.finiteCarrier
  letI : Finite T.support := inferInstance
  have hEvery : EveryIrreducibleEmbedsIn act A
      (s.model.induce T.support T.closed) := by
    exact everyIrreducibleEmbedsIn_induced act A s.model
      (everyIrreducibleEmbedsIn_of_faithful
        act A s.model s.embedding s.isFaithful)
      T.support T.closed
  exact chordal_embedsInFullATree act A
    (s.model.induce T.support T.closed) E
    hfix hcomplete hEvery hNo

/-- When a closed subset of the *next* actual sparsening
stage satisfies the first alternative of the concrete
cycle trichotomy, its induced substructure embeds
exactly into a full-A tree. -/
theorem cycleFreeNext_embeds_fullATree
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.next act A E hfix hcomplete s))
    (hGood : ¬ Sparsening.ContainsInducedCycle s.model E T.support) :
    ∃ (W : Type (max u v)) (H : Structure L W),
      TreeAmalgamation act A H ∧
        Nonempty (Structure.Embedding act
          ((FaithfulSparseningStage.next
            act A E hfix hcomplete s).model.induce
              T.support T.closed) H) := by
  have hNo := sparsening_no_bad_cycle_induced
    s.model E T.support T.closed hGood
  exact embeds_fullATree_of_noBadCycles
    act A E hfix hcomplete
    (FaithfulSparseningStage.next act A E hfix hcomplete s)
    T hNo

/-- **Concrete good ancestor + realisation by `lem:cuts`.**
For every nonempty closed subset of at most n vertices
at level N=n*(n*n+1) of the genuine sparsening tower,
there is an actual closed projected ancestor U at a
positive level, with its certified exact projection chain,
and U embeds into a literal tree of full copies of A.

The original top subset is not yet claimed to embed in
that tree: its projection chain is generally only a
homomorphism-embedding. That composition is the next step. -/
theorem bounded_tower_has_fullATree_ancestor
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (n : ℕ)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.iterate
        act A E hfix hcomplete s (n*(n*n+1))))
    (hNonempty : T.support.Nonempty)
    (hBound : T.support.ncard ≤ n) :
    ∃ (j : ℕ)
      (U : ClosedStageSubset act A
        (FaithfulSparseningStage.iterate
          act A E hfix hcomplete s (j+1))),
      ProjectedAncestor act A E hfix hcomplete s T U ∧
      ∃ (W : Type (max u v)) (H : Structure L W),
        TreeAmalgamation act A H ∧
          Nonempty (Structure.Embedding act
            ((FaithfulSparseningStage.iterate
              act A E hfix hcomplete s (j+1)).model.induce
              U.support U.closed) H) := by
  obtain ⟨j, U, hAncestor, hGood⟩ :=
    cyclefree_ancestor_within_budget
      act A E hfix hcomplete s n T hNonempty hBound
  obtain ⟨W, H, hTree, hEmb⟩ :=
    cycleFreeNext_embeds_fullATree act A E hfix hcomplete
      (FaithfulSparseningStage.iterate
        act A E hfix hcomplete s j)
      U hGood
  exact ⟨j, U, hAncestor, W, H, hTree, hEmb⟩

end ClosedStageSubset
end TreeLike
