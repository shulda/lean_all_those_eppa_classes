import AllThoseEPPA.TreeLikeInfiniteCopiesLocalSideExact
import AllThoseEPPA.TreeLikeInfiniteCopiesGluedHom
import AllThoseEPPA.TreeLikeAmalgamFreeCover

/-!
# Glue actual Γ-homomorphism-embeddings over an aligned interface

The previous construction glued compatible Γ-homomorphisms
h₁:B₁→M and h₂:B₂→M into a Γ-homomorphism of the
concrete free amalgam D=B₁⊕_C B₂.

If both side maps are homomorphism-embeddings, then the glued
map is a homomorphism-embedding as well. Every closed
irreducible substructure S of D lies entirely in the image
of one canonical exact Γ-embedding Bᵢ↪D, including
degenerate amalgamation steps. The exact-side transport
theorem then gives genuine relation reflection, injectivity
on S, and equality of all set-valued function fibres.

No global injectivity of h₁, h₂, or the glued map is used.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y z
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y} {M : Type z}

/-- Compatible Γ-homomorphism-embeddings on the two aligned
sides of an actual Γ-free amalgam glue to a genuine
Γ-homomorphism-embedding on the whole amalgam. -/
theorem amalgamGluedHomomorphism_isHomomorphismEmbedding
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X}
    {B₂ : Structure L Y} {N : Structure L M}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hFG : f.lang = g.lang)
    (h₁ : Structure.Homomorphism act B₁ N)
    (h₂ : Structure.Homomorphism act B₂ N)
    (hLang : h₁.lang = h₂.lang)
    (hAgree : ∀ c : I, h₁ (f c) = h₂ (g c))
    (hh₁ : Structure.Homomorphism.IsHomomorphismEmbedding act h₁)
    (hh₂ : Structure.Homomorphism.IsHomomorphismEmbedding act h₂) :
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (amalgamGluedHomomorphism act f g hFG h₁ h₂ hLang hAgree) := by
  intro S hS hIrr
  have hSide := irreducible_in_amalgam_side act
    f g hFG S hS hIrr
  rcases hSide with hLeft | hRight
  · let j : Structure.Embedding act B₁
        (amalgamStructure act f g hFG) :=
      amalgamLeftEmbedding act f g hFG
    have hjLang :
        (amalgamGluedHomomorphism
          act f g hFG h₁ h₂ hLang hAgree).lang * j.lang =
          h₁.lang := by
      change h₁.lang * 1 = h₁.lang
      simp
    have hjAgree :
        ∀ b : X,
          amalgamGluedHomomorphism
            act f g hFG h₁ h₂ hLang hAgree (j b) = h₁ b := by
      intro b
      rfl
    exact Structure.Homomorphism.isEmbeddingOn_of_embeddedSide
      act j h₁ hh₁
      (amalgamGluedHomomorphism act f g hFG h₁ h₂ hLang hAgree)
      hjLang hjAgree S hS hIrr hLeft
  · let j : Structure.Embedding act B₂
        (amalgamStructure act f g hFG) :=
      amalgamRightEmbedding act f g hFG
    have hjLang :
        (amalgamGluedHomomorphism
          act f g hFG h₁ h₂ hLang hAgree).lang * j.lang =
          h₂.lang := by
      change h₁.lang * 1 = h₂.lang
      simpa using hLang
    have hjAgree :
        ∀ b : Y,
          amalgamGluedHomomorphism
            act f g hFG h₁ h₂ hLang hAgree (j b) = h₂ b := by
      intro b
      exact amalgamGluedHomomorphism_apply_right
        act f g hFG h₁ h₂ hLang hAgree b
    exact Structure.Homomorphism.isEmbeddingOn_of_embeddedSide
      act j h₂ hh₂
      (amalgamGluedHomomorphism act f g hFG h₁ h₂ hLang hAgree)
      hjLang hjAgree S hS hIrr hRight

end TreeLike
end AllThoseEPPA
