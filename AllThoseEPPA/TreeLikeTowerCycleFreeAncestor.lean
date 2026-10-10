import AllThoseEPPA.TreeLikeTowerRankDescent

/-!
# Extract a genuine cycle-free projected ancestor of a small closed subset

The preceding finite-descent proof is not merely about an
arbitrary list of numerical cardinalities: it concerns the
actual canonical projections between the concrete levels
of the iterated sparsening tower.

To make the connection available for the remaining
`thm:maintree` construction, we define the exact
`ProjectedAncestor` relation on two closed subsets:
one is either the original subset at the top level,
or a projected ancestor of the immediate actual
closed backwards projection.

This inductive relation avoids postulating unrelated
witness subsets and tracks an **actual finite chain of
projections**. We prove that failure of the 'all projected
stages have bad cycles' predicate yields such a genuine
projected ancestor free of induced long E-cycles.

Combined with the already bounded-rank descent, a
nonempty closed top-level subset of at most n vertices
in the concrete `n*(n*n+1)`-step tower has an actual
closed cycle-free ancestor.

The next step is to compose the corresponding concrete
homomorphism-embeddings from the initial top subset
to this ancestor, then use the already checked
good-stage-to-full-A-tree theorem and finally transport
the result through the E-reduct.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

namespace ClosedStageSubset

/-- A genuine closed projected ancestor, carrying the
complete chain of *actual* canonical sparsening
projections as an inductive proof. No other subsets can
be constructed by these rules. -/
inductive ProjectedAncestor
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) :
    {k : ℕ} →
      ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s k) →
    {j : ℕ} →
      ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s (j+1)) →
      Prop where
  | newest {j : ℕ}
      (T : ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s (j+1))) :
      ProjectedAncestor act A E hfix hcomplete s T T
  | previous {k j : ℕ}
      (T : ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s (k+1)))
      (U : ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s (j+1)))
      (h : ProjectedAncestor act A E hfix hcomplete s
        (projectAt act A E hfix hcomplete s k T) U) :
      ProjectedAncestor act A E hfix hcomplete s T U

/-- The negation of 'bad cycle at all projected levels'
produces a specific cycle-free *closed subset along the
actual backwards projection chain*, not an unrelated
cycle-free substructure at some arbitrary level. -/
theorem extract_cyclefree_projected_ancestor
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) :
    ∀ (k : ℕ)
      (T : ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s k)),
      ¬ AllProjectedStagesHaveCycles act A E hfix hcomplete s k T →
      ∃ (j : ℕ)
        (U : ClosedStageSubset act A
          (FaithfulSparseningStage.iterate act A E hfix hcomplete s (j+1))),
        ProjectedAncestor act A E hfix hcomplete s T U ∧
          ¬ Sparsening.ContainsInducedCycle
            (FaithfulSparseningStage.iterate act A E hfix hcomplete s j).model
            E U.support := by
  intro k
  induction k with
  | zero =>
      intro T hNot
      exact False.elim (hNot trivial)
  | succ k ih =>
      intro T hNot
      by_cases hGood :
          ¬ Sparsening.ContainsInducedCycle
            (FaithfulSparseningStage.iterate
              act A E hfix hcomplete s k).model E T.support
      · exact ⟨k, T, ProjectedAncestor.newest T, hGood⟩
      · have hBad :
            Sparsening.ContainsInducedCycle
              (FaithfulSparseningStage.iterate
                act A E hfix hcomplete s k).model E T.support :=
          Classical.byContradiction hGood
        let P := projectAt act A E hfix hcomplete s k T
        have hNotP :
            ¬ AllProjectedStagesHaveCycles
              act A E hfix hcomplete s k P := by
          intro hAllP
          exact hNot ⟨hBad, hAllP⟩
        obtain ⟨j, U, hAncestor, hCycleFree⟩ := ih P hNotP
        exact ⟨j, U,
          ProjectedAncestor.previous T U hAncestor, hCycleFree⟩

/-- **Concrete good-stage conclusion of the finite
sparsening rank argument.**
For a nonempty closed subset S of the final structure
obtained from `n*(n*n+1)` actual sparsening steps, there
is a closed projected ancestor, at some positive tower
level, containing **no induced E-cycle of length ≥4**.

The ancestor carries its exact backwards projection
chain as a `ProjectedAncestor` certificate. -/
theorem cyclefree_ancestor_within_budget
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
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s (j+1))),
      ProjectedAncestor act A E hfix hcomplete s T U ∧
        ¬ Sparsening.ContainsInducedCycle
          (FaithfulSparseningStage.iterate
            act A E hfix hcomplete s j).model E U.support := by
  exact extract_cyclefree_projected_ancestor
    act A E hfix hcomplete s
    (n*(n*n+1)) T
    (not_allProjectedStagesHaveCycles
      act A E hfix hcomplete s n T hNonempty hBound)

end ClosedStageSubset
end TreeLike
end AllThoseEPPA
