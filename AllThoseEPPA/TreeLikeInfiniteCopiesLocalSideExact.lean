import AllThoseEPPA.TreeLikeInfiniteCopiesIrreducibleHomEmb
import AllThoseEPPA.FaithfulEmbeddingInverse
import AllThoseEPPA.TreeLikeHomEmbComposition

/-!
# Transport local exactness back through an embedded source side

To prove that a glued homomorphism from a free amalgam is a
homomorphism-embedding, an arbitrary closed irreducible
source S first lies in one exact embedded side j:B↪D.

The restriction of the composite to S factors through the
inverse of j on its closed image and then through a side map
h:B→M. If h is a homomorphism-embedding, the resulting
map on irreducible S is an actual Γ-embedding.

This theorem performs that transport without assuming either
h or the glued map φ is globally injective. It tracks the
possibly nontrivial Γ-component of the source-side inclusion and equality
of all set-valued function fibres on S.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {X : Type w} {Y : Type x} {Z : Type y}

/-- If a homomorphism φ:D→M agrees along an exact Γ-embedding
j:B↪D (with arbitrary Γ-language component) with
a homomorphism-embedding h:B→M, then φ is an exact embedding
on every *closed irreducible subset S entirely inside j(B)*. -/
theorem isEmbeddingOn_of_embeddedSide
    (act : L.Action Γ)
    {B : Structure L X} {D : Structure L Y}
    {M : Structure L Z}
    (j : Embedding act B D)
    (h : Homomorphism act B M)
    (hHomEmb : IsHomomorphismEmbedding act h)
    (φ : Homomorphism act D M)
    (hLang : φ.lang * j.lang = h.lang)
    (hAgree : ∀ b : X, φ (j b) = h b)
    (S : Set Y) (hS : D.IsClosed S)
    (hIrr : (D.induce S hS).IsIrreducible)
    (hInside : S ⊆ Set.range j.toFun) :
    IsEmbeddingOn act φ S := by
  classical
  let k : Embedding act (D.induce S hS) B :=
    Faithful.embeddingInverseOnClosedSubset act j S hS hInside
  have hkLang : k.lang = j.lang⁻¹ := rfl
  have hkHomEmb : IsHomomorphismEmbedding act k.toHomomorphism := by
    intro T hT hIrrT
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb hab
      exact k.injective hab
    · intro n R xs hxs
      exact k.map_rel_iff R xs
    · intro n F xs hxs
      exact k.map_func F xs
  let comp : Homomorphism act (D.induce S hS) M :=
    h.comp k.toHomomorphism
  have hComp : IsHomomorphismEmbedding act comp :=
    comp_isHomomorphismEmbedding act h k.toHomomorphism
      hHomEmb hkHomEmb
  let e : Embedding act (D.induce S hS) M :=
    toEmbedding_of_irreducible act comp hComp hIrr
  have heLang : e.lang = φ.lang := by
    change h.lang * k.lang = φ.lang
    rw [hkLang]
    calc
      h.lang * j.lang⁻¹ = (φ.lang * j.lang) * j.lang⁻¹ := by rw [hLang]
      _ = φ.lang := by simp [mul_assoc]
  have heApply (z : S) : φ z.1 = e z := by
    have hBack :=
      Faithful.embeddingInverseOnClosedSubset_apply_spec
        act j S hS hInside z
    calc
      φ z.1 = φ (j (k z)) := congrArg φ.toFun hBack.symm
      _ = h (k z) := hAgree (k z)
      _ = e z := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    have hEq : (⟨a, ha⟩ : S) = ⟨b, hb⟩ := by
      apply e.injective
      calc
        e ⟨a, ha⟩ = φ a := (heApply ⟨a, ha⟩).symm
        _ = φ b := hab
        _ = e ⟨b, hb⟩ := heApply ⟨b, hb⟩
    exact congrArg Subtype.val hEq
  · intro n R xs hxs
    let ys : Fin n → S := fun i => ⟨xs i, hxs i⟩
    have hRel := e.map_rel_iff R ys
    have hyTuple : e.toFun ∘ ys = φ.toFun ∘ xs := by
      funext i
      exact (heApply (ys i)).symm
    have hxTuple : Subtype.val ∘ ys = xs := rfl
    change M.rel (act.onRel e.lang R) (e.toFun ∘ ys) ↔
      D.rel R (Subtype.val ∘ ys) at hRel
    rw [heLang, hyTuple, hxTuple] at hRel
    exact hRel
  · intro n F xs hxs
    let ys : Fin n → S := fun i => ⟨xs i, hxs i⟩
    have hyTuple : e.toFun ∘ ys = φ.toFun ∘ xs := by
      funext i
      exact (heApply (ys i)).symm
    have hxTuple : Subtype.val ∘ ys = xs := rfl
    have hImage :
        imageSet φ.toFun (D.func F xs) =
          imageSet e.toFun ((D.induce S hS).func F ys) := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        have haS : a ∈ S := hS F xs hxs ha
        refine ⟨⟨a, haS⟩, ?_, ?_⟩
        · change a ∈ D.func F (Subtype.val ∘ ys)
          rw [hxTuple]
          exact ha
        · exact (heApply ⟨a, haS⟩).symm
      · rintro ⟨a, ha, rfl⟩
        refine ⟨a.1, ?_, ?_⟩
        · change a.1 ∈ D.func F (Subtype.val ∘ ys) at ha
          rw [hxTuple] at ha
          exact ha
        · exact heApply a
    have hf := e.map_func F ys
    change imageSet e.toFun ((D.induce S hS).func F ys) =
      M.func (act.onFunc e.lang F) (e.toFun ∘ ys) at hf
    rw [heLang, hyTuple] at hf
    exact hImage.trans hf

end Homomorphism
end Structure
end AllThoseEPPA
