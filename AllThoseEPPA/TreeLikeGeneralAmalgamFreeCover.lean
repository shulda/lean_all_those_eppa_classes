import AllThoseEPPA.TreeLikeAmalgamGeneral
import AllThoseEPPA.TreeLikeAmalgamFreeCover

/-!
# Irreducible side localization for arbitrary Γ-amalgamations

`irreducible_in_amalgam_side` proved locality when the two
interface embeddings have equal language components. The
actual tree-amalgamation definition uses
`generalAmalgamStructure`, which accepts **arbitrary**
Γ-embeddings and aligns their language components by
relabelling one whole side.

The relabelling changes no vertices, so the previously
proved irreducible-localization theorem transfers directly
to the two canonical embeddings of the original structures.
This is the precise general-language interface needed for
induction over `TreeAmalgamation`.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- An irreducible closed induced substructure of the
explicit **general-Γ** amalgam always lies wholly inside
one original embedded source, including degenerate attachments
and distinct initial language components. -/
theorem generalAmalgam_irreducible_in_side
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (S : Set (AmalgamCarrier f.toFun g.toFun))
    (hS : (generalAmalgamStructure act f g).IsClosed S)
    (hIrr :
      ((generalAmalgamStructure act f g).induce S hS).IsIrreducible) :
    S ⊆ Set.range (generalAmalgamLeftEmbedding act f g).toFun ∨
      S ⊆ Set.range (generalAmalgamRightEmbedding act f g).toFun := by
  have hLocal :=
    irreducible_in_amalgam_side act
      f (alignedRightEmbedding act f g)
      (alignedRightEmbedding_lang_eq act f g)
      S hS hIrr
  have hLeft :
      (generalAmalgamLeftEmbedding act f g).toFun =
        amalgamLeft f.toFun g.toFun := by
    funext x
    exact generalAmalgamLeftEmbedding_apply act f g x
  have hRight :
      (generalAmalgamRightEmbedding act f g).toFun =
        amalgamRight f.toFun g.toFun := by
    funext y
    exact generalAmalgamRightEmbedding_apply act f g y
  rw [hLeft, hRight]
  exact hLocal

end TreeLike
end AllThoseEPPA
