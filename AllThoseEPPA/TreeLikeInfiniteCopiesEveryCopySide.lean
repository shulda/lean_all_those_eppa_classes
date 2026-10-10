import AllThoseEPPA.TreeLikeGeneralAmalgamFreeCover
import AllThoseEPPA.TreeLikeIrreducibleEmbeddingImage
import AllThoseEPPA.TreeLikeEmbeddingFactorComposition

/-!
# Factor any irreducible A-copy in a general Γ-amalgam through one side

The "moreover" conclusion of Lemma lem:infinitecopies
requires handling *every* embedded full A-copy in a tree
amalgamation, not only those used in its construction.

If A is irreducible and α:A↪D embeds A into a concrete
general Γ-free amalgam D=B₁⊕_C B₂, its closed
irreducible image lies inside one of the exact embedded
source sides. The already checked exact Γ-factorization
lemma therefore gives α=jᵢ∘βᵢ as an equality of
**full Γ-embeddings**, not merely of vertex maps.

This is valid for arbitrary arity of relations and
set-valued functions and for nontrivial language actions.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y z
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y} {V : Type z}

/-- Any embedded copy of an irreducible A inside an actual
general Γ-free amalgam factors *exactly*, including the
language component, through one canonical embedded source. -/
theorem irreducibleCopy_factors_generalAmalgam_side
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X}
    {B₂ : Structure L Y} {A : Structure L V}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hA : A.IsIrreducible)
    (α : Structure.Embedding act A
      (generalAmalgamStructure act f g)) :
    (∃ β₁ : Structure.Embedding act A B₁,
      (generalAmalgamLeftEmbedding act f g).comp β₁ = α) ∨
    (∃ β₂ : Structure.Embedding act A B₂,
      (generalAmalgamRightEmbedding act f g).comp β₂ = α) := by
  let D := generalAmalgamStructure act f g
  let S : Set (AmalgamCarrier f.toFun g.toFun) :=
    Set.range α.toFun
  let hS : D.IsClosed S := α.range_isClosed act
  have hIrr : (D.induce S hS).IsIrreducible :=
    α.range_isIrreducible act hA
  rcases generalAmalgam_irreducible_in_side
    act f g S hS hIrr with hLeft | hRight
  · let j : Structure.Embedding act B₁ D :=
      generalAmalgamLeftEmbedding act f g
    have hRange : ∀ a : V, ∃ b : X, j b = α a := by
      intro a
      exact hLeft ⟨a, rfl⟩
    let β₁ : Structure.Embedding act A B₁ :=
      j.factorThrough act α hRange
    exact Or.inl ⟨β₁,
      Structure.Embedding.comp_factorThrough act j α hRange⟩
  · let j : Structure.Embedding act B₂ D :=
      generalAmalgamRightEmbedding act f g
    have hRange : ∀ a : V, ∃ b : Y, j b = α a := by
      intro a
      exact hRight ⟨a, rfl⟩
    let β₂ : Structure.Embedding act A B₂ :=
      j.factorThrough act α hRange
    exact Or.inr ⟨β₂,
      Structure.Embedding.comp_factorThrough act j α hRange⟩

end TreeLike
end AllThoseEPPA
