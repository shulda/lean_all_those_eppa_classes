import AllThoseEPPA.TreeLikeTowerClosedProjections

/-!
# Backward projection along any finite segment of a sparsening tower

The preceding development constructs a genuine finite tower of
cycle-sparsening EPPA witnesses and proves that one projection
maps a closed subset to a closed subset, without increasing its
vertex count and without destroying nonemptiness.

Here we construct the *iterated* backwards image over any
number of successive tower levels, preserving that closure
as part of the returned data and proving that neither the
vertex count nor nonemptiness can deteriorate.

This dependent recursion supplies an actual sequence of closed
induced structures at arbitrary levels, instead of a
hypothetical sequence assumed in the numerical rank lemma.
The remaining theorem `thm:maintree` must apply the actual
sparsening trichotomy at each of these levels and identify a
cycle-free one by finite descent.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

namespace ClosedStageSubset

/-- Project an arbitrary closed subset on tower level
`start + steps` backwards through exactly `steps`
canonical sparsening maps. The output is automatically a
closed subset of the earlier level `start`. -/
noncomputable def projectDown
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (start : ℕ) :
    (steps : ℕ) →
      ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s
          (start + steps)) →
      ClosedStageSubset act A
        (FaithfulSparseningStage.iterate act A E hfix hcomplete s start)
  | 0, T => T
  | steps + 1, T =>
      projectDown act A E hfix hcomplete s start steps
        (projectAt act A E hfix hcomplete s (start + steps) T)

/-- Any iterated backwards projection of a closed subset
has no more vertices than the original top-level set.
This combines the genuine `k+1 → k` cardinal bounds,
not an abstract monotonicity assumption. -/
theorem projectDown_ncard_le
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (start steps : ℕ)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.iterate act A E hfix hcomplete s
        (start + steps))) :
    (projectDown act A E hfix hcomplete s start steps T).support.ncard ≤
      T.support.ncard := by
  induction steps generalizing T with
  | zero =>
      exact le_refl _
  | succ steps ih =>
      let P :=
        projectAt act A E hfix hcomplete s (start + steps) T
      exact (ih P).trans
        (projectAt_ncard_le act A E hfix hcomplete s
          (start + steps) T)

/-- Nonempty vertex sets remain nonempty through *every*
backwards projection, even though the individual projections
need not be injective. -/
theorem projectDown_nonempty
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (start steps : ℕ)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.iterate act A E hfix hcomplete s
        (start + steps)))
    (hT : T.support.Nonempty) :
    (projectDown act A E hfix hcomplete s start steps T).support.Nonempty := by
  induction steps generalizing T with
  | zero =>
      exact hT
  | succ steps ih =>
      let s' := FaithfulSparseningStage.iterate
        act A E hfix hcomplete s (start + steps)
      let P : ClosedStageSubset act A s' :=
        projectAt act A E hfix hcomplete s (start + steps) T
      have hP : P.support.Nonempty :=
        project_nonempty act A E hfix hcomplete s' T hT
      exact ih P hP

end ClosedStageSubset
end TreeLike
end AllThoseEPPA
