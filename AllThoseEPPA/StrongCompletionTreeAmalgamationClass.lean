import AllThoseEPPA.StrongCompletionIrreducibleCopyEPPA
import AllThoseEPPA.TreeLikeFullAAmalgamation
import AllThoseEPPA.TreeLikeInfiniteCopiesSurjectiveInverse
import AllThoseEPPA.TreeLikeInfiniteCopiesGeneralGluedHomEmb

/-!
# Observation 9.4: completing literal tree amalgamations

We encode only the *amalgamation* part of a finite Γ-class:
a predicate on structures of a chosen common carrier universe,
together with an amalgamation operation returning a finite
member and two compatible genuine Γ-embeddings.

Heredity and irreducibility of class members, which are
additional hypotheses of Theorem 1.6, are not needed for
Observation 9.4 itself.

For finite irreducible A in an amalgamation class K, every
literal recursive tree amalgamation of full A-copies admits a
homomorphism-embedding to some finite member of K.

The key point is that recursively obtained side homomorphism-
embeddings are **exact on the designated A-copies**, because A
is irreducible. Their images therefore provide legitimate
interfaces for the next amalgamation, and the already checked
general Γ-gluing theorem combines the two sides.

This handles all relation/function arities and nontrivial
Γ-language permutations.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} {Γ : Type w} [Group Γ]

/-- Abstract finite-target amalgamation interface for Γ-structures.
The class may contain structures of heterogeneous carrier types,
and the amalgamation is required to preserve the full language
component as well as pointwise interface agreement. -/
structure FiniteAmalgamationClass
    (act : L.Action Γ) where
  mem : {V : Type v} → Structure L V → Prop
  amalgamate :
    ∀ {I X Y : Type v}
      {D : Structure L I} {B₁ : Structure L X}
      {B₂ : Structure L Y}
      (f : Structure.Embedding act D B₁)
      (g : Structure.Embedding act D B₂),
      mem B₁ → mem B₂ →
      ∃ (Z : Type v) (_ : Finite Z) (B : Structure L Z),
        mem B ∧
        ∃ (j₁ : Structure.Embedding act B₁ B)
          (j₂ : Structure.Embedding act B₂ B),
          j₁.comp f = j₂.comp g

variable {U : Type v}

/-- **Manuscript Observation 9.4.**
Every actual tree amalgamation D of copies of a finite
irreducible A homomorphism-embeds in a finite member of
any Γ-amalgamation class containing A.

No finite forbidden families, auxiliary E, or automorphism
extension properties are required. -/
theorem TreeAmalgamation.completesInAmalgamationClass
    (act : L.Action Γ)
    (A : Structure L U) [Finite U]
    (hA : A.IsIrreducible)
    (K : FiniteAmalgamationClass act)
    (hKA : K.mem A)
    {V : Type v} {D : Structure L V}
    (hTree : TreeAmalgamation act A D) :
    ∃ (Z : Type v) (_ : Finite Z) (B : Structure L Z),
      K.mem B ∧
      ∃ f : Structure.Homomorphism act D B,
        Structure.Homomorphism.IsHomomorphismEmbedding act f := by
  classical
  induction hTree with
  | copy C e hSurj =>
      let inverse : Structure.Embedding act C A :=
        e.inverseSurjective act hSurj
      refine ⟨U, inferInstance, A, hKA, inverse.toHomomorphism, ?_⟩
      exact Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding
        act inverse
  | glue C B₁ B₂ hT₁ hT₂ δ₁ δ₂ α₁ α₂ ih₁ ih₂ =>
      obtain ⟨Z₁, hZ₁, E₁, hE₁, f₁, hf₁⟩ := ih₁
      obtain ⟨Z₂, hZ₂, E₂, hE₂, f₂, hf₂⟩ := ih₂
      let α₁' : Structure.Embedding act A E₁ :=
        Structure.Homomorphism.compEmbedding_of_irreducible
          act f₁ hf₁ α₁ hA
      let α₂' : Structure.Embedding act A E₂ :=
        Structure.Homomorphism.compEmbedding_of_irreducible
          act f₂ hf₂ α₂ hA
      let q₁ : Structure.Embedding act C E₁ := α₁'.comp δ₁
      let q₂ : Structure.Embedding act C E₂ := α₂'.comp δ₂
      obtain ⟨Z, hZ, E, hE, j₁, j₂, hGlue⟩ :=
        K.amalgamate q₁ q₂ hE₁ hE₂
      let t₁ : Structure.Homomorphism act B₁ E :=
        j₁.toHomomorphism.comp f₁
      let t₂ : Structure.Homomorphism act B₂ E :=
        j₂.toHomomorphism.comp f₂
      have ht₁ : Structure.Homomorphism.IsHomomorphismEmbedding act t₁ :=
        Structure.Homomorphism.comp_isHomomorphismEmbedding
          act j₁.toHomomorphism f₁
          (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding
            act j₁) hf₁
      have ht₂ : Structure.Homomorphism.IsHomomorphismEmbedding act t₂ :=
        Structure.Homomorphism.comp_isHomomorphismEmbedding
          act j₂.toHomomorphism f₂
          (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding
            act j₂) hf₂
      have hGlueLang :
          j₁.lang * ((f₁.lang * α₁.lang) * δ₁.lang) =
          j₂.lang * ((f₂.lang * α₂.lang) * δ₂.lang) := by
        have h := congrArg
          (fun z : Structure.Embedding act C E => z.lang) hGlue
        exact h
      have hLang :
          t₁.lang * (α₁.comp δ₁).lang =
          t₂.lang * (α₂.comp δ₂).lang := by
        change (j₁.lang * f₁.lang) * (α₁.lang * δ₁.lang) =
          (j₂.lang * f₂.lang) * (α₂.lang * δ₂.lang)
        calc
          (j₁.lang * f₁.lang) * (α₁.lang * δ₁.lang) =
              j₁.lang * ((f₁.lang * α₁.lang) * δ₁.lang) := by
            simp [mul_assoc]
          _ = j₂.lang * ((f₂.lang * α₂.lang) * δ₂.lang) :=
            hGlueLang
          _ = (j₂.lang * f₂.lang) * (α₂.lang * δ₂.lang) := by
            simp [mul_assoc]
      have hAgree :
          ∀ c, t₁ ((α₁.comp δ₁) c) =
            t₂ ((α₂.comp δ₂) c) := by
        intro c
        have h := congrArg
          (fun z : Structure.Embedding act C E => z c) hGlue
        exact h
      let t : Structure.Homomorphism act
          (generalAmalgamStructure act
            (α₁.comp δ₁) (α₂.comp δ₂)) E :=
        generalAmalgamGluedHomomorphism act
          (α₁.comp δ₁) (α₂.comp δ₂) t₁ t₂ hLang hAgree
      have ht : Structure.Homomorphism.IsHomomorphismEmbedding act t :=
        generalAmalgamGluedHomomorphism_isHomomorphismEmbedding
          act (α₁.comp δ₁) (α₂.comp δ₂)
          t₁ t₂ hLang hAgree ht₁ ht₂
      exact ⟨Z, hZ, E, hE, t, ht⟩

end TreeLike
end AllThoseEPPA
