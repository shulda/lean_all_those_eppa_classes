import AllThoseEPPA.TreeLikeAmalgamCarrier
import AllThoseEPPA.Relabelling

/-!
# Align the language components of two amalgamation embeddings

The concrete carrier of a free amalgam is determined by underlying
injective maps, but a Γ-structure embedding also has a language
permutation. Before amalgamating two Γ-structures along embeddings
`f : C ↪ B₁` and `g : C ↪ B₂`, one can relabel B₂ by
`f.lang * g.lang⁻¹`. The same underlying vertex map g then
has language component f.lang.

This step is essential for interpreting relations and set-valued
functions on the two sides consistently, even for nontrivial
language actions. It is a checked equality, not a convention that
all embeddings preserve language symbols literally.
-/

namespace AllThoseEPPA
namespace Structure
namespace Embedding

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Relabel the *target* of a Γ-embedding by k. The same map of
vertices remains an exact embedding with language component
k * f.lang. This works with arbitrary set-valued functions. -/
def relabelTarget
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B) (k : Γ) :
    Embedding act A (B.relabel act k) where
  lang := k * f.lang
  toFun := f.toFun
  injective := f.injective
  map_rel_iff := by
    intro n R xs
    change B.rel (act.onRel k⁻¹
        (act.onRel (k * f.lang) R)) (f.toFun ∘ xs) ↔ A.rel R xs
    have hk : k⁻¹ * (k * f.lang) = f.lang := by
      simp [mul_assoc]
    rw [← act.onRel_mul, hk]
    exact f.map_rel_iff R xs
  map_func := by
    intro n F xs
    change imageSet f.toFun (A.func F xs) =
      B.func (act.onFunc k⁻¹
        (act.onFunc (k * f.lang) F)) (f.toFun ∘ xs)
    have hk : k⁻¹ * (k * f.lang) = f.lang := by
      simp [mul_assoc]
    rw [← act.onFunc_mul, hk]
    exact f.map_func F xs

@[simp] theorem relabelTarget_lang
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B) (k : Γ) :
    (f.relabelTarget act k).lang = k * f.lang :=
  rfl

end Embedding
end Structure

namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- After relabelling B₂, the two maps from C into B₁ and
B₂ have the **same language component**, as needed by the
definition of a free amalgam. -/
def alignedRightEmbedding
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) :
    Structure.Embedding act C
      (B₂.relabel act (f.lang * g.lang⁻¹)) :=
  g.relabelTarget act (f.lang * g.lang⁻¹)

/-- Relabelling genuinely aligns the permutation components. -/
@[simp] theorem alignedRightEmbedding_lang
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) :
    (alignedRightEmbedding act f g).lang = f.lang := by
  simp [alignedRightEmbedding, mul_assoc]

/-- Alignment does not modify the underlying vertex map. -/
@[simp] theorem alignedRightEmbedding_apply
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (x : I) :
    alignedRightEmbedding act f g x = g x :=
  rfl

end TreeLike
end AllThoseEPPA
