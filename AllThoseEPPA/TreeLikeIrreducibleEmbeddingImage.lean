import AllThoseEPPA.TreeLikeIrreducibilityTransport
import AllThoseEPPA.TreeLikeEmbeddingRangeClosure

/-!
# Exact embeddings carry irreducibles onto irreducible induced images

The tree-amalgamation observation needs to move an irreducible
closed substructure of an amalgam into one of its embedded
source structures. The image of a genuine Γ-embedding is
function-closed, and the structure induced on the image is
Γ-isomorphic to the source.

This file constructs that isomorphism as a *surjective exact
Γ-embedding* and transfers irreducibility by the previous
Γ-isomorphism theorem. No symmetry of the language, no unary
restriction, and no identity-language assumption are required.
-/

namespace AllThoseEPPA
namespace Structure
namespace Embedding

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Any exact Γ-embedding factors through its closed induced
range via a *surjective* Γ-embedding. All relation and function
interpretations are preserved in both directions. -/
noncomputable def toClosedRange
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B) :
    Embedding act A
      (B.induce (Set.range f.toFun) (f.range_isClosed act)) where
  lang := f.lang
  toFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
  injective := by
    intro a b h
    apply f.injective
    exact congrArg Subtype.val h
  map_rel_iff := by
    intro n R xs
    change B.rel (act.onRel f.lang R) (f.toFun ∘ xs) ↔
      A.rel R xs
    exact f.map_rel_iff R xs
  map_func := by
    intro n F xs
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      change f a ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ xs)
      have hfa : f a ∈ imageSet f.toFun (A.func F xs) :=
        ⟨a, ha, rfl⟩
      rw [f.map_func F xs] at hfa
      exact hfa
    · intro hy
      change y.1 ∈ B.func (act.onFunc f.lang F)
        (f.toFun ∘ xs) at hy
      rw [← f.map_func F xs] at hy
      obtain ⟨a, ha, hfa⟩ := hy
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      exact hfa

/-- The induced-range embedding genuinely covers the whole
induced range. -/
theorem toClosedRange_surjective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B) :
    Function.Surjective (f.toClosedRange act).toFun := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha⟩ := hb
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

/-- Exact Γ-structure embeddings send irreducible structures
onto irreducible closed induced substructures of their targets.
This is the transport required for the later recursive
tree-of-A-copies argument. -/
theorem range_isIrreducible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B)
    (hIrr : A.IsIrreducible) :
    (B.induce (Set.range f.toFun)
      (f.range_isClosed act)).IsIrreducible := by
  exact irreducible_of_surjective act
    (f.toClosedRange act) (toClosedRange_surjective act f) hIrr

end Embedding
end Structure
end AllThoseEPPA
