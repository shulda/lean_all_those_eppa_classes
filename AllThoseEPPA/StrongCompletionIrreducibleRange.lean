import AllThoseEPPA.TreeLikeEmbeddingRangeClosure
import AllThoseEPPA.TreeLikeIrreducibilityTransport

/-!
# Exact embedded ranges of irreducible structures

The image of an exact Γ-embedding is function-closed even in a
language with arbitrary set-valued functions. Here we package the
canonical Γ-embedding *onto the induced range* and its surjectivity.

Consequently the image of an irreducible source under an embedding
is irreducible. This is a crucial interface for strong completion:
a homomorphism-embedding need only be exact on irreducible closed
substructures, but the original distinguished A-copy in a witness
is such a substructure when A is irreducible.
-/

namespace AllThoseEPPA
namespace Structure
namespace Embedding

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- An exact Γ-embedding onto the genuinely induced structure
on its entire function-closed image. -/
def toClosedRange
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (e : Embedding act A B) :
    Embedding act A (B.induce (Set.range e.toFun)
      (e.range_isClosed act)) where
  lang := e.lang
  toFun := fun a => ⟨e a, a, rfl⟩
  injective := by
    intro a b hab
    exact e.injective (congrArg Subtype.val hab)
  map_rel_iff := by
    intro n R xs
    exact e.map_rel_iff R xs
  map_func := by
    intro n F xs
    ext y
    constructor
    · rintro ⟨a, ha, hay⟩
      have hImage : e a ∈
          imageSet e.toFun (A.func F xs) := ⟨a, ha, rfl⟩
      rw [e.map_func F xs] at hImage
      have hEq : e a = y.1 := congrArg Subtype.val hay
      rw [hEq] at hImage
      exact hImage
    · intro hy
      have hImage :
          y.1 ∈ imageSet e.toFun (A.func F xs) := by
        rw [e.map_func F xs]
        exact hy
      obtain ⟨a, ha, hay⟩ := hImage
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      exact hay

/-- The image embedding is surjective, with no finiteness
or trivial-language-action assumptions. -/
theorem toClosedRange_surjective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (e : Embedding act A B) :
    Function.Surjective (e.toClosedRange act).toFun := by
  intro y
  obtain ⟨a, ha⟩ := y.2
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

/-- Irreducibility survives the exact closed image of an
embedding with potentially nontrivial Γ-language component. -/
theorem closedRange_irreducible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (e : Embedding act A B)
    (hIrr : A.IsIrreducible) :
    (B.induce (Set.range e.toFun)
      (e.range_isClosed act)).IsIrreducible := by
  exact irreducible_of_surjective act
    (e.toClosedRange act)
    (e.toClosedRange_surjective act) hIrr

end Embedding
end Structure
end AllThoseEPPA
