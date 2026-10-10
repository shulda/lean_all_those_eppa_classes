import AllThoseEPPA.TreeLikeTowerConcreteRank
import AllThoseEPPA.TreeLikeTowerClosedProjections
import AllThoseEPPA.TreeLikeEdgeBudget
import Mathlib.Data.Set.Card
import Lean.Elab.Tactic.Omega

/-!
# A bad sparsening stage cannot persist through the entire finite tower

The exact finite sparsening tower is now constructed from actual EPPA
witnesses, and each backwards projection of a closed subset is
again closed. The concrete rank-trichotomy lemma proves a strict
rank increase at any stage which contains a long induced E-cycle.

This file packages the **actual recursively projected subsets** as
a proposition `AllProjectedStagesHaveCycles`: the subset at level
k contains a bad cycle, and its precise backwards image at level
k-1 has the same property, recursively down to the starting level.

If the final subset is nonempty and has at most n vertices, then
this predicate cannot hold for a tower with `n*(n*n+1)`
sparsening steps. The proof inductively bounds the index of
a uniformly increasing natural-number rank, and contradicts
the previously checked square budget on directed E-edge pairs.

This is a concrete instance of the finite-descent principle,
not an assumed numerical sequence. The subsequent theorem
will extract a specific intermediate cycle-free closed subset
along with its projection ancestry, compose the intermediate
homomorphism-embeddings, and invoke the proved `lem:cuts`.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

namespace ClosedStageSubset

/-- Actual `all steps are bad` predicate for the backwards
projections of one top-level closed subset, not an abstract
sequence of sets unrelated to the sparsening tower. -/
def AllProjectedStagesHaveCycles
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) :
    (k : ℕ) →
      ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s k) →
      Prop
  | 0, _ => True
  | k+1, T =>
      Sparsening.ContainsInducedCycle
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s k).model
        E T.support ∧
      AllProjectedStagesHaveCycles act A E hfix hcomplete s
        k (projectAt act A E hfix hcomplete s k T)

/-- If all actual projected subsets at levels 1,...,k
contain long induced cycles, a nonempty top-level subset
of size at most n must have bounded rank at least k.

This is the exact proof that the numerical rank descent
works for the concrete dependent sparsening tower. -/
theorem allProjectedCycles_rank_ge_index
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (n : ℕ) :
    ∀ (k : ℕ)
      (T : ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s k)),
      AllProjectedStagesHaveCycles act A E hfix hcomplete s k T →
      T.support.Nonempty →
      T.support.ncard ≤ n →
      k ≤ sparseningRank (n*n) T.support.ncard
        (Nat.card (Sparsening.EdgePairs
          (FaithfulSparseningStage.iterate act A E hfix hcomplete s k).model
          E T.support)) := by
  intro k
  induction k with
  | zero =>
      intro T hAll hNonempty hBound
      exact Nat.zero_le _
  | succ k ih =>
      intro T hAll hNonempty hBound
      let sk := FaithfulSparseningStage.iterate
        act A E hfix hcomplete s k
      let P : ClosedStageSubset act A sk :=
        projectAt act A E hfix hcomplete s k T
      have hCycle :
          Sparsening.ContainsInducedCycle sk.model E T.support :=
        hAll.1
      have hAllP :
          AllProjectedStagesHaveCycles act A E hfix hcomplete s k P :=
        hAll.2
      have hNonemptyP : P.support.Nonempty :=
        project_nonempty act A E hfix hcomplete sk T hNonempty
      have hBoundP : P.support.ncard ≤ n :=
        (projectAt_ncard_le act A E hfix hcomplete s k T).trans hBound
      have hPrevious := ih P hAllP hNonemptyP hBoundP
      have hStep :
          sparseningRank (n*n) P.support.ncard
            (Nat.card (Sparsening.EdgePairs sk.model E P.support)) <
          sparseningRank (n*n) T.support.ncard
            (Nat.card (Sparsening.EdgePairs
              (FaithfulSparseningStage.iterate
                act A E hfix hcomplete s (k+1)).model E T.support)) := by
        rcases closedTower_concrete_rank_progress
            act A E hfix hcomplete s k n T hNonempty hBound with
          hGood | hRise
        · exact False.elim (hGood hCycle)
        · exact hRise
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hPrevious hStep)

/-- After `n*(n*n+1)` concrete sparsening steps, the
backwards projections of any nonempty closed top subset
on at most n vertices **cannot all contain bad cycles**.

The proof uses the actual stage ranks, monotonic cardinalities,
and the checked directed E-edge budget. No abstract sequence
or additional compactness principle is assumed. -/
theorem not_allProjectedStagesHaveCycles
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
    ¬ AllProjectedStagesHaveCycles
      act A E hfix hcomplete s (n*(n*n+1)) T := by
  intro hAll
  let k := n*(n*n+1)
  let sk := FaithfulSparseningStage.iterate
    act A E hfix hcomplete s k
  letI : Finite sk.Carrier := sk.finiteCarrier
  have hPos : 1 ≤ T.support.ncard :=
    (Set.ncard_pos (Set.toFinite T.support)).mpr hNonempty
  have hEdges :
      Nat.card (Sparsening.EdgePairs sk.model E T.support) ≤ n*n :=
    edgePairs_card_le_budget sk.model E T.support n hBound
  have hRankGe :
      k ≤ sparseningRank (n*n) T.support.ncard
        (Nat.card (Sparsening.EdgePairs sk.model E T.support)) :=
    allProjectedCycles_rank_ge_index act A E hfix hcomplete
      s n k T hAll hNonempty hBound
  have hRankLt :
      sparseningRank (n*n) T.support.ncard
        (Nat.card (Sparsening.EdgePairs sk.model E T.support)) < k :=
    sparseningRank_lt_budget n (n*n)
      T.support.ncard
      (Nat.card (Sparsening.EdgePairs sk.model E T.support))
      hPos hBound hEdges
  exact (not_lt_of_ge hRankGe) hRankLt

end ClosedStageSubset
end TreeLike
end AllThoseEPPA
