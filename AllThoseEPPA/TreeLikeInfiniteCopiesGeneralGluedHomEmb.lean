import AllThoseEPPA.TreeLikeInfiniteCopiesLocalSideExact
import AllThoseEPPA.TreeLikeInfiniteCopiesGeneralGluedHom
import AllThoseEPPA.TreeLikeGeneralAmalgamFreeCover

/-!
# Arbitrary Γ-free amalgams glue Γ-homomorphism-embeddings

The general Γ-amalgam aligns the language of its second side
by k=f.lang*g.lang⁻¹. The corresponding canonical exact
embedding of the ORIGINAL second side therefore carries this
language component (rather than 1).

After constructing the actual Γ-homomorphism into M from
compatible maps h₁ and h₂, every closed irreducible source
is supported in one of these *original* embedded sides.
The general embedded-side local-exactness lemma works even
when this inclusion has nonidentity Γ-language component.

Thus the target maps need not be globally injective, and
no identity action assumption is hidden in the gluing step.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y z
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y} {M : Type z}

/-- The genuine Γ-language component of the second source
inclusion in a general Γ-free amalgam. -/
@[simp] theorem generalAmalgamRightEmbedding_lang
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X}
    {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) :
    (generalAmalgamRightEmbedding act f g).lang =
      f.lang * g.lang⁻¹ := by
  change 1 * ((f.lang * g.lang⁻¹) * 1) = f.lang * g.lang⁻¹
  simp

/-- The honest Γ-homomorphism from the general amalgam
into M is a Γ-homomorphism-*embedding* if both source
maps are such and their composites agree on the interface,
including their Γ-language components. -/
theorem generalAmalgamGluedHomomorphism_isHomomorphismEmbedding
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X}
    {B₂ : Structure L Y} {N : Structure L M}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (h₁ : Structure.Homomorphism act B₁ N)
    (h₂ : Structure.Homomorphism act B₂ N)
    (hLang : h₁.lang * f.lang = h₂.lang * g.lang)
    (hAgree : ∀ c : I, h₁ (f c) = h₂ (g c))
    (hh₁ : Structure.Homomorphism.IsHomomorphismEmbedding act h₁)
    (hh₂ : Structure.Homomorphism.IsHomomorphismEmbedding act h₂) :
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (generalAmalgamGluedHomomorphism
        act f g h₁ h₂ hLang hAgree) := by
  intro S hS hIrr
  have hSide := generalAmalgam_irreducible_in_side
    act f g S hS hIrr
  rcases hSide with hLeft | hRight
  · let j : Structure.Embedding act B₁
        (generalAmalgamStructure act f g) :=
      generalAmalgamLeftEmbedding act f g
    have hjLang :
        (generalAmalgamGluedHomomorphism
          act f g h₁ h₂ hLang hAgree).lang * j.lang =
          h₁.lang := by
      change h₁.lang * 1 = h₁.lang
      simp
    have hjAgree :
        ∀ b : X,
          generalAmalgamGluedHomomorphism
            act f g h₁ h₂ hLang hAgree (j b) = h₁ b := by
      intro b
      rfl
    exact Structure.Homomorphism.isEmbeddingOn_of_embeddedSide
      act j h₁ hh₁
      (generalAmalgamGluedHomomorphism act f g h₁ h₂ hLang hAgree)
      hjLang hjAgree S hS hIrr hLeft
  · let j : Structure.Embedding act B₂
        (generalAmalgamStructure act f g) :=
      generalAmalgamRightEmbedding act f g
    have hLangR :
        h₁.lang * (f.lang * g.lang⁻¹) = h₂.lang := by
      calc
        h₁.lang * (f.lang * g.lang⁻¹) =
            (h₁.lang * f.lang) * g.lang⁻¹ := by
          simp [mul_assoc]
        _ = (h₂.lang * g.lang) * g.lang⁻¹ := by
          rw [hLang]
        _ = h₂.lang := by simp [mul_assoc]
    have hjLang :
        (generalAmalgamGluedHomomorphism
          act f g h₁ h₂ hLang hAgree).lang * j.lang =
          h₂.lang := by
      change h₁.lang * j.lang = h₂.lang
      rw [show j.lang = f.lang * g.lang⁻¹ from
        generalAmalgamRightEmbedding_lang act f g]
      exact hLangR
    have hjAgree :
        ∀ b : Y,
          generalAmalgamGluedHomomorphism
            act f g h₁ h₂ hLang hAgree (j b) = h₂ b := by
      intro b
      change gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun
        (amalgamRight f.toFun g.toFun b) = h₂ b
      exact gluedCarrierMap_right f.toFun g.toFun g.injective
        h₁.toFun h₂.toFun hAgree b
    exact Structure.Homomorphism.isEmbeddingOn_of_embeddedSide
      act j h₂ hh₂
      (generalAmalgamGluedHomomorphism act f g h₁ h₂ hLang hAgree)
      hjLang hjAgree S hS hIrr hRight

end TreeLike
end AllThoseEPPA
