import AllThoseEPPA.TreeLikeInfiniteCopiesAlignM
import AllThoseEPPA.TreeLikeInfiniteCopiesAmbientPostcompose

/-!
# Align two normalized tree-side homomorphism-embeddings in M

The tree induction in lem:infinitecopies uses side maps
hᵢ:Bᵢ→M which, after ambient automorphisms σᵢ,
agree *pointwise* with the distinguished embedded A-copy
along the selected embeddings αᵢ:A↪Bᵢ.

To glue the two sides over embeddings δ₁,δ₂:C↪A,
extend the canonical interface partial automorphism of A
to an ambient automorphism u of M. The side maps
u∘σ₁∘h₁ and σ₂∘h₂ then agree on the actual
amalgamation interface, **including Γ-language elements**.

Both new maps remain homomorphism-embeddings by the
previously checked ambient-automorphism postcomposition
theorem. This statement performs the essential Γ-group
calculation independently of the later free-amalgam
homomorphism-embedding gluing theorem.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y z
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {V : Type x} {X : Type y} {Y : Type z}
variable {M : Type (max u v w x y z)}

/-- From two homomorphism-embeddings already normalized on their
chosen full-A copies, construct compatible side maps into M by
extending the canonical interface partial automorphism.

There are no finiteness or function-arity restrictions. -/
theorem exists_compatible_normalizedSideMaps
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
    ∃ (l : Structure.Homomorphism act B₁ N)
      (r : Structure.Homomorphism act B₂ N),
      Structure.Homomorphism.IsHomomorphismEmbedding act l ∧
      Structure.Homomorphism.IsHomomorphismEmbedding act r ∧
      l.lang * (α₁.comp δ₁).lang =
        r.lang * (α₂.comp δ₂).lang ∧
      (∀ c : I, l ((α₁.comp δ₁) c) = r ((α₂.comp δ₂) c)) := by
  obtain ⟨u, huLang, huApply⟩ :=
    exists_ambientAutomorphism_aligning_interface
      act a hExt δ₁ δ₂
  let l₀ : Structure.Homomorphism act B₁ N :=
    (σ₁.toEmbedding act).toHomomorphism.comp h₁
  let l : Structure.Homomorphism act B₁ N :=
    (u.toEmbedding act).toHomomorphism.comp l₀
  let r : Structure.Homomorphism act B₂ N :=
    (σ₂.toEmbedding act).toHomomorphism.comp h₂
  have hl₀ : Structure.Homomorphism.IsHomomorphismEmbedding act l₀ :=
    Structure.Homomorphism.postcompose_automorphism_isHomomorphismEmbedding
      act h₁ hh₁ σ₁
  have hl : Structure.Homomorphism.IsHomomorphismEmbedding act l :=
    Structure.Homomorphism.postcompose_automorphism_isHomomorphismEmbedding
      act l₀ hl₀ u
  have hr : Structure.Homomorphism.IsHomomorphismEmbedding act r :=
    Structure.Homomorphism.postcompose_automorphism_isHomomorphismEmbedding
      act h₂ hh₂ σ₂
  refine ⟨l, r, hl, hr, ?_, ?_⟩
  · change
      (u.lang * (σ₁.lang * h₁.lang)) * (α₁.lang * δ₁.lang) =
        (σ₂.lang * h₂.lang) * (α₂.lang * δ₂.lang)
    calc
      (u.lang * (σ₁.lang * h₁.lang)) * (α₁.lang * δ₁.lang) =
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

end TreeLike
end AllThoseEPPA
