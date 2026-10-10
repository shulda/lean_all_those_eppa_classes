import AllThoseEPPA.TreeLikeAmalgamCompatibility

/-!
# Candidate free amalgam structure on the explicit glued carrier

Given two Γ-embeddings of C whose language components agree, the
source structures admit a concrete amalgam presentation. Its
carrier was built in `TreeLikeAmalgamCarrier`; here we interpret:

* a relation tuple exactly when it is the image of a relation
  tuple from one of the two sides;
* a function value exactly when it is the image of a function
  value from a side containing **the entire input tuple**.

There are no cross-side relation or function configurations.
The chosen equality of the language components ensures the two
interpretations agree over C, as checked in
`TreeLikeAmalgamCompatibility`.

This first module proves source **homomorphisms** into the candidate
amalgam, with the *actual pointwise maps* on the glued carrier.
The stronger exact-embedding and `FreeDecomposition` certificates
are subsequent proof obligations; neither is assumed as an axiom.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- Concrete Γ-structure on the glued carrier of two embeddings
with aligned language components. All interpretations are induced
from the source structures, with empty cross-side function fibres. -/
noncomputable def amalgamStructure
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang) :
    Structure L (AmalgamCarrier f.toFun g.toFun) where
  rel := by
    intro n R zs
    exact
      (∃ xs : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ xs = zs ∧ B₁.rel R xs) ∨
      (∃ ys : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ ys = zs ∧ B₂.rel R ys)
  func := by
    intro n F zs
    exact
      { z | ∃ xs : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ xs = zs ∧
        z ∈ Structure.imageSet (amalgamLeft f.toFun g.toFun)
          (B₁.func F xs) } ∪
      { z | ∃ ys : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ ys = zs ∧
        z ∈ Structure.imageSet (amalgamRight f.toFun g.toFun)
          (B₂.func F ys) }

/-- The left structure maps homomorphically into the candidate
amalgam. This is independent of the later reflection theorem. -/
noncomputable def amalgamLeftHom
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang) :
    Structure.Homomorphism act B₁
      (amalgamStructure act f g hLang) where
  lang := 1
  toFun := amalgamLeft f.toFun g.toFun
  map_rel := by
    intro n R xs hRel
    change
      (∃ xs' : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ xs' =
          amalgamLeft f.toFun g.toFun ∘ xs ∧ B₁.rel R xs') ∨
      (∃ ys : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ ys =
          amalgamLeft f.toFun g.toFun ∘ xs ∧ B₂.rel R ys)
    exact Or.inl ⟨xs, rfl, hRel⟩
  map_func := by
    intro n F xs z hz
    change
      (∃ xs' : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ xs' =
          amalgamLeft f.toFun g.toFun ∘ xs ∧
        z ∈ Structure.imageSet (amalgamLeft f.toFun g.toFun)
          (B₁.func F xs')) ∨
      (∃ ys : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ ys =
          amalgamLeft f.toFun g.toFun ∘ xs ∧
        z ∈ Structure.imageSet (amalgamRight f.toFun g.toFun)
          (B₂.func F ys))
    exact Or.inl ⟨xs, rfl, hz⟩

/-- The right structure also maps homomorphically into the same
amalgam using its glued inclusion. The two source maps agree on
every point of C by `amalgamRight_glued`. -/
noncomputable def amalgamRightHom
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang) :
    Structure.Homomorphism act B₂
      (amalgamStructure act f g hLang) where
  lang := 1
  toFun := amalgamRight f.toFun g.toFun
  map_rel := by
    intro n R ys hRel
    change
      (∃ xs : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ xs =
          amalgamRight f.toFun g.toFun ∘ ys ∧ B₁.rel R xs) ∨
      (∃ ys' : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ ys' =
          amalgamRight f.toFun g.toFun ∘ ys ∧ B₂.rel R ys')
    exact Or.inr ⟨ys, rfl, hRel⟩
  map_func := by
    intro n F ys z hz
    change
      (∃ xs : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ xs =
          amalgamRight f.toFun g.toFun ∘ ys ∧
        z ∈ Structure.imageSet (amalgamLeft f.toFun g.toFun)
          (B₁.func F xs)) ∨
      (∃ ys' : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ ys' =
          amalgamRight f.toFun g.toFun ∘ ys ∧
        z ∈ Structure.imageSet (amalgamRight f.toFun g.toFun)
          (B₂.func F ys'))
    exact Or.inr ⟨ys, rfl, hz⟩

end TreeLike
end AllThoseEPPA
