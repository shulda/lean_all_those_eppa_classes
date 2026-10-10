import AllThoseEPPA.TreeLikeHomEmbClosedIrreducibleImage

/-!
# Composition of homomorphism-embeddings

A composition of arbitrary homomorphisms need not be an
embedding. In the paper's EPPA machinery, however, each
sparsening projection is a **homomorphism-embedding**:
on every irreducible closed substructure, it is a
genuine embedding (both relation directions, exact
set-valued-function fibres, local injectivity).

The composition remains a homomorphism-embedding. The
essential reason is that an irreducible substructure S
is sent by the first map to a *closed irreducible* image
T; hence the second map also embeds T exactly.
`TreeLikeHomEmbClosedIrreducibleImage` proves precisely
this image theorem without global injectivity.

This makes arbitrary compositions of the typed
homomorphism-embeddings along the actual sparsening
tower legitimate, even when the successive projections
collapse vertices outside the particular irreducible
substructure being considered.

All function symbols may have arbitrary arity and
genuinely set-valued interpretations.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x} {X : Type y}

/-- The class of homomorphism-embeddings is closed under
composition for any Γ-language action and set-valued
function symbols of arbitrary arity. This is the
fundamental structural composition lemma needed for
the final `thm:maintree` projection chain. -/
theorem comp_isHomomorphismEmbedding
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W} {C : Structure L X}
    (g : Homomorphism act B C)
    (f : Homomorphism act A B)
    (hG : IsHomomorphismEmbedding act g)
    (hF : IsHomomorphismEmbedding act f) :
    IsHomomorphismEmbedding act (g.comp f) := by
  intro S hS hIrr
  have hLocalF : IsEmbeddingOn act f S :=
    hF S hS hIrr
  let T : Set W := imageSet f.toFun S
  let hT : B.IsClosed T :=
    image_isClosed_of_embeddingOn act f S hS hLocalF
  have hIrrT : (B.induce T hT).IsIrreducible :=
    image_isIrreducible_of_embeddingOn act f S hS hLocalF hIrr
  have hLocalG : IsEmbeddingOn act g T :=
    hG T hT hIrrT
  have hInT : ∀ (a : V), a ∈ S → f a ∈ T := by
    intro a ha
    exact ⟨a, ha, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    apply hLocalF.1 ha hb
    exact hLocalG.1 (hInT a ha) (hInT b hb) hab
  · intro n R xs hxs
    have hfTuple : ∀ i, (f.toFun ∘ xs) i ∈ T :=
      fun i => hInT (xs i) (hxs i)
    have hRelG := hLocalG.2.1
      (act.onRel f.lang R) (f.toFun ∘ xs) hfTuple
    have hRelF := hLocalF.2.1 R xs hxs
    simpa only [Homomorphism.comp, Language.Action.onRel_mul,
      Function.comp_assoc] using hRelG.trans hRelF
  · intro n F xs hxs
    have hfTuple : ∀ i, (f.toFun ∘ xs) i ∈ T :=
      fun i => hInT (xs i) (hxs i)
    have hFuncF := hLocalF.2.2 F xs hxs
    have hFuncG := hLocalG.2.2
      (act.onFunc f.lang F) (f.toFun ∘ xs) hfTuple
    change imageSet (g.toFun ∘ f.toFun) (A.func F xs) =
      C.func (act.onFunc (g.lang * f.lang) F)
        ((g.toFun ∘ f.toFun) ∘ xs)
    calc
      imageSet (g.toFun ∘ f.toFun) (A.func F xs) =
        imageSet g.toFun (imageSet f.toFun (A.func F xs)) :=
          imageSet_comp g.toFun f.toFun (A.func F xs)
      _ = imageSet g.toFun
            (B.func (act.onFunc f.lang F) (f.toFun ∘ xs)) := by
          rw [hFuncF]
      _ = C.func (act.onFunc g.lang (act.onFunc f.lang F))
            (g.toFun ∘ (f.toFun ∘ xs)) :=
          hFuncG
      _ = C.func (act.onFunc (g.lang * f.lang) F)
            ((g.toFun ∘ f.toFun) ∘ xs) := by
          rw [← Language.Action.onFunc_mul]
          rfl

end Homomorphism
end Structure
end AllThoseEPPA
