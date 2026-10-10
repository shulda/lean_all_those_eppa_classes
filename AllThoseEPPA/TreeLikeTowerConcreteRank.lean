import AllThoseEPPA.TreeLikeTowerClosedProjections
import AllThoseEPPA.TreeLikeConcreteSparseningRank

/-!
# Apply the concrete rank trichotomy to the actual closed tower levels

The two already checked post-`lem:cuts` developments are:

* a genuine finite tower of canonical cycle-sparsening structures,
  with a closed subset at each stage projected backwards;
* the *concrete* sparsening-trichotomy-to-rank theorem, using
  the uniform square budget for ordered E-edge pairs.

This file connects them without postulating an abstract
sequence. For every nonempty closed subset of level k+1
containing at most n vertices, either it is free of long
induced E-cycles, or the rank **strictly increases**
from its exact closed projection at level k to its current
level. This is the one-step property required for the
finite numerical descent theorem `exists_good_sparsening_step`.

The final theorem `thm:maintree` will extract all the closed
subsets backwards from a chosen small substructure, then use
boundedness of this rank to force a good cycle-free stage,
apply the proved `lem:cuts`, and compose the intermediate
homomorphism-embeddings.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

/-- Actual cycle trichotomy on a nonempty closed subset T
of the immediate sparsening successor of one finite faithful
EPPA stage: either T is cycle-free, or the rank of its exact
closed backwards image is strictly smaller than T's rank. -/
theorem closedStage_concrete_rank_progress
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.next act A E hfix hcomplete s))
    (n : ℕ)
    (hNonempty : T.support.Nonempty)
    (hBound : T.support.ncard ≤ n) :
    ¬ Sparsening.ContainsInducedCycle s.model E T.support ∨
      sparseningRank (n * n)
        (ClosedStageSubset.project act A E hfix hcomplete s T).support.ncard
        (Nat.card (Sparsening.EdgePairs s.model E
          (ClosedStageSubset.project act A E hfix hcomplete s T).support)) <
      sparseningRank (n * n)
        T.support.ncard
        (Nat.card (Sparsening.EdgePairs
          (FaithfulSparseningStage.next act A E hfix hcomplete s).model
          E T.support)) := by
  letI : Finite s.Carrier := s.finiteCarrier
  exact concrete_sparsening_rank_progress
    s.model E T.support n hNonempty hBound

/-- Concrete rank progress **between the actual levels
k and k+1** in any finite tower constructed by repeatedly
applying the checked cycle-sparsening lemma. No abstract
sequence is assumed in this formulation. -/
theorem closedTower_concrete_rank_progress
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (k n : ℕ)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.iterate act A E hfix hcomplete s (k+1)))
    (hNonempty : T.support.Nonempty)
    (hBound : T.support.ncard ≤ n) :
    ¬ Sparsening.ContainsInducedCycle
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s k).model
        E T.support ∨
      sparseningRank (n * n)
        (ClosedStageSubset.projectAt act A E hfix hcomplete s k T).support.ncard
        (Nat.card (Sparsening.EdgePairs
          (FaithfulSparseningStage.iterate act A E hfix hcomplete s k).model
          E (ClosedStageSubset.projectAt act A E hfix hcomplete s k T).support)) <
      sparseningRank (n * n)
        T.support.ncard
        (Nat.card (Sparsening.EdgePairs
          (FaithfulSparseningStage.iterate act A E hfix hcomplete s (k+1)).model
          E T.support)) := by
  exact closedStage_concrete_rank_progress act A E hfix hcomplete
    (FaithfulSparseningStage.iterate act A E hfix hcomplete s k)
    T n hNonempty hBound

end TreeLike
end AllThoseEPPA
