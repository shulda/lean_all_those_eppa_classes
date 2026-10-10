import AllThoseEPPA.TreeLikeAmalgamGeneral
import AllThoseEPPA.TreeLikeFreeCutBaseEmbeddings

/-!
# Exact language components of the Γ-free-amalgam maps

To glue embeddings of the left and right sides of a free
decomposition of B, it is essential that the two **composite**
embeddings into the constructed amalgam have the same language
component, even if the original side embeddings have different
language permutations.

The explicit general-Γ amalgam achieves this by applying the
permutation `f.lang * g.lang⁻¹` to the right source. This file
records the exact component and checks algebraically that it
indeed aligns the two composite embeddings. The canonical
embeddings of a free-cut common base into either induced side
have trivial language component.
-/

namespace AllThoseEPPA

namespace TreeLike
universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- The actual first source embeds with identity language
component into the newly constructed Γ-amalgam. -/
@[simp] theorem generalAmalgamLeftEmbedding_lang
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) :
    (generalAmalgamLeftEmbedding act f g).lang = 1 :=
  rfl

/-- The second source embedding has precisely the language
relabeling required to align the two maps of the interface. -/
@[simp] theorem generalAmalgamRightEmbedding_lang
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) :
    (generalAmalgamRightEmbedding act f g).lang =
      f.lang * g.lang⁻¹ := by
  simp [generalAmalgamRightEmbedding,
    Structure.Embedding.comp, Structure.Embedding.relabelTarget,
    Structure.Embedding.id]

universe z
variable {V : Type z}

/-- The shared free-cut base is included into the left side
with identity Γ-language component, despite its definition
through exact embedding factorization. -/
@[simp] theorem freeCut_baseToLeft_lang
    (act : L.Action Γ) (B : Structure L V)
    (d : B.FreeDecomposition) :
    (freeCut_baseToLeft act B d).lang = 1 := by
  simp [freeCut_baseToLeft, Structure.Embedding.factorThrough,
    Structure.inclusion]

/-- The corresponding right inclusion has the same identity
language component. -/
@[simp] theorem freeCut_baseToRight_lang
    (act : L.Action Γ) (B : Structure L V)
    (d : B.FreeDecomposition) :
    (freeCut_baseToRight act B d).lang = 1 := by
  simp [freeCut_baseToRight, Structure.Embedding.factorThrough,
    Structure.inclusion]

end TreeLike
end AllThoseEPPA
