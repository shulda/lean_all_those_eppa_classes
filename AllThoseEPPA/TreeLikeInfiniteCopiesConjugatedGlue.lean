import AllThoseEPPA.TreeLikeInfiniteCopiesNormalizedGlue
import AllThoseEPPA.TreeLikeInfiniteCopiesAmbientPostcompose

/-!
# Compatible normalized sides with explicit ambient conjugations

The tree induction in manuscript Lemma lem:infinitecopies needs
to transport the normalization invariant for *every* embedded
A-copy through the eventual glued map. Merely exhibiting
compatible homomorphism-embeddings l and r is not enough:
we must also retain that l = τ₁ ∘ h₁ and r = τ₂ ∘ h₂
for concrete ambient Γ-automorphisms τ₁ and τ₂.

This module strengthens the already checked normalized-side
alignment theorem to return those automorphisms and their
actual Γ-language and pointwise equations. This avoids a
hidden appeal to unlabelled vertex permutations.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y z t
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {V : Type x} {X : Type y}
variable {Y : Type z} {M : Type t}

/-- Choose side maps with both the compatibility conditions and
explicit witnesses that each map is an ambient automorphism
postcomposition of its original homomorphism-embedding. -/
theorem exists_compatible_normalizedSideMaps_withConjugations
    (act : L.Action Γ)
    {C : Structure L I} {A : Structure L V}
    {B₁ : Structure L X} {B₂ : Structure L Y}
    {N : Structure L M}
    (a : Structure.Embedding act A N)
    (hExt : ∀ p : Structure.PartialAutomorphism act A,
      ∃ g : Structure.Automorphism act N,
        Structure.ExtendsAlong act a p g)
    (α₁ : Structure.Embedding act A B₁)
    (α₂ : Structure.Embedding act A B₂)
    (δ₁ δ₂ : Structure.Embedding act C A)
    (h₁ : Structure.Homomorphism act B₁ N)
    (h₂ : Structure.Homomorphism act B₂ N)
    (hh₁ : Structure.Homomorphism.IsHomomorphismEmbedding act h₁)
    (hh₂ : Structure.Homomorphism.IsHomomorphismEmbedding act h₂)
    (σ₁ σ₂ : Structure.Automorphism act N)
    (hLang₁ : σ₁.lang * h₁.lang * α₁.lang = a.lang)
    (hLang₂ : σ₂.lang * h₂.lang * α₂.lang = a.lang)
    (hApply₁ : ∀ x : V, σ₁ (h₁ (α₁ x)) = a x)
    (hApply₂ : ∀ x : V, σ₂ (h₂ (α₂ x)) = a x) :
    ∃ (τ₁ τ₂ : Structure.Automorphism act N)
      (l : Structure.Homomorphism act B₁ N)
      (r : Structure.Homomorphism act B₂ N),
      Structure.Homomorphism.IsHomomorphismEmbedding act l ∧
      Structure.Homomorphism.IsHomomorphismEmbedding act r ∧
      l.lang * (α₁.comp δ₁).lang =
        r.lang * (α₂.comp δ₂).lang ∧
      (∀ c : I, l ((α₁.comp δ₁) c) = r ((α₂.comp δ₂) c)) ∧
      l.lang = τ₁.lang * h₁.lang ∧
      (∀ x : X, l x = τ₁ (h₁ x)) ∧
      r.lang = τ₂.lang * h₂.lang ∧
      (∀ y : Y, r y = τ₂ (h₂ y)) := by
  obtain ⟨u, huLang, huApply⟩ :=
    exists_ambientAutomorphism_aligning_interface
      act a hExt δ₁ δ₂
  let τ₁ : Structure.Automorphism act N := u.comp σ₁
  let τ₂ : Structure.Automorphism act N := σ₂
  let l : Structure.Homomorphism act B₁ N :=
    (τ₁.toEmbedding act).toHomomorphism.comp h₁
  let r : Structure.Homomorphism act B₂ N :=
    (τ₂.toEmbedding act).toHomomorphism.comp h₂
  have hl : Structure.Homomorphism.IsHomomorphismEmbedding act l :=
    Structure.Homomorphism.postcompose_automorphism_isHomomorphismEmbedding
      act h₁ hh₁ τ₁
  have hr : Structure.Homomorphism.IsHomomorphismEmbedding act r :=
    Structure.Homomorphism.postcompose_automorphism_isHomomorphismEmbedding
      act h₂ hh₂ τ₂
  refine ⟨τ₁, τ₂, l, r, hl, hr, ?_, ?_, rfl, ?_, rfl, ?_⟩
  · change
      ((u.lang * σ₁.lang) * h₁.lang) * (α₁.lang * δ₁.lang) =
        (σ₂.lang * h₂.lang) * (α₂.lang * δ₂.lang)
    calc
      ((u.lang * σ₁.lang) * h₁.lang) * (α₁.lang * δ₁.lang) =
          (u.lang * (σ₁.lang * h₁.lang * α₁.lang)) * δ₁.lang := by
            simp [mul_assoc]
      _ = (u.lang * a.lang) * δ₁.lang := by rw [hLang₁]
      _ = (a.lang * (δ₂.lang * δ₁.lang⁻¹)) * δ₁.lang := by rw [huLang]
      _ = a.lang * δ₂.lang := by simp [mul_assoc]
      _ = (σ₂.lang * h₂.lang * α₂.lang) * δ₂.lang := by rw [hLang₂]
      _ = (σ₂.lang * h₂.lang) * (α₂.lang * δ₂.lang) := by
        simp [mul_assoc]
  · intro c
    change u (σ₁ (h₁ (α₁ (δ₁ c)))) =
      σ₂ (h₂ (α₂ (δ₂ c)))
    calc
      u (σ₁ (h₁ (α₁ (δ₁ c)))) = u (a (δ₁ c)) := by rw [hApply₁]
      _ = a (δ₂ c) := huApply c
      _ = σ₂ (h₂ (α₂ (δ₂ c))) := (hApply₂ (δ₂ c)).symm
  · intro x
    rfl
  · intro y
    rfl

end TreeLike
end AllThoseEPPA
