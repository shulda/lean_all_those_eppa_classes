import AllThoseEPPA.UnaryHomEmbImageClosure

/-!
# Exact factorization through the closed image of a unary Γ-hom-embedding

Forbidding homomorphism-embeddings into an EPPA witness
requires restricting the witness to the actual image of a
finite forbidden structure F. The preceding theorem
proves that this image is function-closed when all
functions are unary.

Here we construct the induced image structure itself and
a genuine Γ-homomorphism-embedding of F into it. Global
injectivity of the original map is NOT needed: exact
reflection is required only on each irreducible closed
source substructure, and that property survives passing
to the codomain's induced closed image.

This bridge makes the image a legitimate small closed
substructure to which the local tree property of
`thm:maintree` can be applied.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- The Γ-homomorphism into the actual closed induced range of a
homomorphism-embedding in a unary-function language. -/
def toClosedRange_unary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f) :
    Homomorphism act A
      (B.induce (Set.range f.toFun)
        (range_isClosed_of_unary act f hf)) where
  lang := f.lang
  toFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
  map_rel := by
    intro n R xs hrel
    exact f.map_rel R xs hrel
  map_func := by
    intro n F xs z hz
    rcases hz with ⟨a, ha, rfl⟩
    change f a ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ xs)
    exact f.map_func F xs ⟨a, ha, rfl⟩

/-- Factoring through the closed image preserves the entire
Γ-homomorphism-embedding condition, including exact equality
of every set-valued function fibre on each irreducible
closed source substructure. -/
theorem toClosedRange_unary_isHomomorphismEmbedding
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f) :
    IsHomomorphismEmbedding act (f.toClosedRange_unary act hf) := by
  intro T hT hIrr
  have hExact := hf T hT hIrr
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact hExact.1 ha hb (congrArg Subtype.val hab)
  · intro n R xs hxs
    exact hExact.2.1 R xs hxs
  · intro n F xs hxs
    apply Set.ext
    intro y
    constructor
    · rintro ⟨a, ha, hay⟩
      have hm : f a ∈ imageSet f.toFun (A.func F xs) :=
        ⟨a, ha, rfl⟩
      rw [hExact.2.2 F xs hxs] at hm
      have heq : f a = y.1 := congrArg Subtype.val hay
      rw [heq] at hm
      exact hm
    · intro hy
      have hm : y.1 ∈ B.func (act.onFunc f.lang F)
          (f.toFun ∘ xs) := hy
      rw [← hExact.2.2 F xs hxs] at hm
      obtain ⟨a, ha, hay⟩ := hm
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      exact hay

end Homomorphism
end Structure
end AllThoseEPPA
