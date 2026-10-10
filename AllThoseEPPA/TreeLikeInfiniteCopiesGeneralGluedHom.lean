import AllThoseEPPA.TreeLikeInfiniteCopiesGluedHom
import AllThoseEPPA.TreeLikeInfiniteCopiesRelabelHom
import AllThoseEPPA.TreeLikeAmalgamGeneral

/-!
# Glue Γ-homomorphisms with arbitrary interface language components

The manuscript's recursive tree amalgamations use a general Γ-free
amalgam over embeddings f:C↪B₁ and g:C↪B₂ whose language
components need not agree. The concrete general amalgam aligns
the second copy by k = f.lang * g.lang⁻¹.

A pair of Γ-homomorphisms h₁:B₁→M and h₂:B₂→M can
therefore be glued if their *composites from C* have the same
Γ-language component and their vertex maps agree on C:

  h₁.lang * f.lang = h₂.lang * g.lang,
  h₁(f c) = h₂(g c).

The relabelled second-side homomorphism has language component
h₂.lang * k⁻¹ = h₁.lang, making the aligned gluing theorem
applicable. The resulting actual Γ-homomorphism maps into M,
with exact group bookkeeping rather than a trivial-language
shortcut. The subsequent local homomorphism-embedding condition
still requires irreducible-side transport.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y z
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y} {M : Type z}

/-- The Γ-homomorphism out of a *general* Γ-free amalgam,
glued from compatible side homomorphisms after the necessary
language relabelling of the second source. -/
noncomputable def generalAmalgamGluedHomomorphism
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X}
    {B₂ : Structure L Y} {N : Structure L M}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (h₁ : Structure.Homomorphism act B₁ N)
    (h₂ : Structure.Homomorphism act B₂ N)
    (hLang : h₁.lang * f.lang = h₂.lang * g.lang)
    (hAgree : ∀ c : I, h₁ (f c) = h₂ (g c)) :
    Structure.Homomorphism act (generalAmalgamStructure act f g) N := by
  let k : Γ := f.lang * g.lang⁻¹
  let g' : Structure.Embedding act C (B₂.relabel act k) :=
    alignedRightEmbedding act f g
  let h₂' : Structure.Homomorphism act (B₂.relabel act k) N :=
    h₂.relabelSource act k
  have hCorrectLang : h₁.lang = h₂'.lang := by
    change h₁.lang = h₂.lang * (f.lang * g.lang⁻¹)⁻¹
    calc
      h₁.lang = (h₁.lang * f.lang) * f.lang⁻¹ := by
        simp [mul_assoc]
      _ = (h₂.lang * g.lang) * f.lang⁻¹ := by
        rw [hLang]
      _ = h₂.lang * (f.lang * g.lang⁻¹)⁻¹ := by
        simp [mul_inv_rev, mul_assoc]
  have hCorrectAgree : ∀ c : I, h₁ (f c) = h₂' (g' c) := by
    intro c
    exact hAgree c
  exact amalgamGluedHomomorphism act f g'
    (alignedRightEmbedding_lang_eq act f g)
    h₁ h₂' hCorrectLang hCorrectAgree

end TreeLike
end AllThoseEPPA
