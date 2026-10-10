import AllThoseEPPA.TreeLikeTowerAncestorHomEmb
import AllThoseEPPA.TreeLikeFiniteSparseningTower

/-!
# Homomorphism-embedding back to the original sparsening witness

The restricted EPPA theorem in the manuscript asks not only
for local maps into trees, but also for one global
homomorphism-embedding of the new EPPA witness back into the
given initial EPPA witness.

Every step in the *actual* finite sparsening tower has a
homomorphism-embedding projection. The composition theorem
on arbitrary closed irreducible sources permits an exact
iteration of these canonical projections, without assuming
that the maps are globally injective.

This builds the concrete map, retaining its Γ-language
component and exact set-valued function fibres on each
irreducible substructure.
-/

namespace AllThoseEPPA
namespace TreeLike
namespace FaithfulSparseningStage

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

/-- An explicit composite of the canonical homomorphisms
from level k to the starting level 0. It is not a chosen
map obtained merely from an existence assertion. -/
noncomputable def iterateProjectionToInitial
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) :
    (k : ℕ) →
    Structure.Homomorphism act
      (iterate act A E hfix hcomplete s k).model s.model
  | 0 => Structure.Homomorphism.id (act := act) s.model
  | k + 1 =>
      (iterateProjectionToInitial act A E hfix hcomplete s k).comp
        (iterateProjection act A E hfix hcomplete s k)

/-- The concrete iterated projection is a homomorphism-embedding:
on each irreducible closed substructure its restriction is
injective and reflects every relation and the full image
of each set-valued function fibre. -/
theorem iterateProjectionToInitial_isHomomorphismEmbedding
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) (k : ℕ) :
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (iterateProjectionToInitial act A E hfix hcomplete s k) := by
  induction k with
  | zero =>
      exact Structure.Homomorphism.id_isHomomorphismEmbedding
        act s.model
  | succ k ih =>
      exact Structure.Homomorphism.comp_isHomomorphismEmbedding
        act
        (iterateProjectionToInitial act A E hfix hcomplete s k)
        (iterateProjection act A E hfix hcomplete s k)
        ih
        (nextProjection_isHomomorphismEmbedding act A E hfix hcomplete
          (iterate act A E hfix hcomplete s k))

end FaithfulSparseningStage
end TreeLike
end AllThoseEPPA
