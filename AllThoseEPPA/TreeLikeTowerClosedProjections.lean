import AllThoseEPPA.TreeLikeFiniteSparseningTower
import AllThoseEPPA.CycleSparseningProjectionImage
import Mathlib.Data.Set.Card

/-!
# Closed small subsets transported backwards in an actual sparsening tower

The finite tower from `TreeLikeFiniteSparseningTower` consists of
concrete Γ-structures and actual sparsening projections. A crucial
feature of the unary-function setting is that these projections
map every function fibre **onto** the corresponding old fibre,
so the image of a closed subset is closed even though the
projection need not be injective.

This file packages closed subsets of a stage and constructs
their projection one step backwards, proving:

* the backwards image is a genuine closed induced substructure;
* it has at most as many vertices as the newer subset;
* if the newer subset is nonempty, so is the projection;
* the same operations work between levels k+1 and k of the
  actual dependently typed tower.

These are the exact hypotheses needed for applying the bounded
rank/descent theorem across iterated sparsening levels.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

/-- A closed set of vertices of one concrete finite
faithful EPPA stage, retaining the proof of function
closure so that it can be induced as a genuine substructure. -/
structure ClosedStageSubset
    (act : L.Action Γ) (A : Structure L α)
    (s : FaithfulSparseningStage act A) where
  support : Set s.Carrier
  closed : s.model.IsClosed support

namespace ClosedStageSubset

/-- Project a closed subset of the next sparsening witness
back into the preceding stage, without assuming injectivity
or genericity of the subset. -/
noncomputable def project
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.next act A E hfix hcomplete s)) :
    ClosedStageSubset act A s := by
  letI : Finite s.Carrier := s.finiteCarrier
  exact
    { support := Sparsening.projectionImage s.model E T.support
      closed :=
        Sparsening.projectionImage_isClosed
          act s.model E T.support T.closed }

/-- The projection does not increase the number of vertices
of any closed subset; this is a standard cardinality fact
but is recorded with the precise tower types. -/
theorem project_ncard_le
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.next act A E hfix hcomplete s)) :
    (project act A E hfix hcomplete s T).support.ncard ≤
      T.support.ncard := by
  letI : Finite s.Carrier := s.finiteCarrier
  letI : Finite
      (FaithfulSparseningStage.next act A E hfix hcomplete s).Carrier :=
    (FaithfulSparseningStage.next act A E hfix hcomplete s).finiteCarrier
  change
    (Sparsening.projectionImage s.model E T.support).ncard ≤
      T.support.ncard
  exact Set.ncard_image_le (Set.toFinite T.support)

/-- A nonempty set cannot have an empty projection. -/
theorem project_nonempty
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.next act A E hfix hcomplete s))
    (hNonempty : T.support.Nonempty) :
    (project act A E hfix hcomplete s T).support.Nonempty := by
  letI : Finite s.Carrier := s.finiteCarrier
  obtain ⟨w, hw⟩ := hNonempty
  change (Sparsening.projectionImage s.model E T.support).Nonempty
  exact ⟨w.base s.model E, ⟨w, hw, rfl⟩⟩

/-- Backwards projection between the actual levels k+1 and k
of an iterated finite faithful sparsening tower. -/
noncomputable def projectAt
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (k : ℕ)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.iterate act A E hfix hcomplete s (k+1))) :
    ClosedStageSubset act A
      (FaithfulSparseningStage.iterate act A E hfix hcomplete s k) :=
  project act A E hfix hcomplete
    (FaithfulSparseningStage.iterate act A E hfix hcomplete s k) T

/-- Every backwards step of the actual tower does not
increase the number of projected vertices. -/
theorem projectAt_ncard_le
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (k : ℕ)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.iterate act A E hfix hcomplete s (k+1))) :
    (projectAt act A E hfix hcomplete s k T).support.ncard ≤
      T.support.ncard :=
  project_ncard_le act A E hfix hcomplete
    (FaithfulSparseningStage.iterate act A E hfix hcomplete s k) T

end ClosedStageSubset
end TreeLike
end AllThoseEPPA
