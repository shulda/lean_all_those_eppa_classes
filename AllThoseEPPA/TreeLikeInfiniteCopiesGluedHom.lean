import AllThoseEPPA.TreeLikeInfiniteCopiesGlueCarrier
import AllThoseEPPA.TreeLikeAmalgamStructure

/-!
# Glue compatible Γ-homomorphisms from two amalgamation sides

For the induction in lem:infinitecopies, we need more than a
piecewise vertex map. Suppose f:C↪B₁ and g:C↪B₂ are
Γ-embeddings with matching language components, and
h₁:B₁→M and h₂:B₂→M are Γ-homomorphisms with
matching language components and agreeing on the gluing
interface. They induce an actual Γ-homomorphism of the
concrete free amalgam B₁ ⊕_C B₂ into M.

The proof checks both kinds of relation tuples and all
set-valued function fibres on each side separately. It does
not assume h₁ or h₂ injective. The stronger conclusion that
this glued map is a homomorphism-*embedding* needs separate
irreducible-side localization; it is not asserted here.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y z
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y} {M : Type z}

/-- The actual Γ-homomorphism obtained by gluing compatible
side Γ-homomorphisms into the same target structure M. -/
noncomputable def amalgamGluedHomomorphism
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X}
    {B₂ : Structure L Y} {N : Structure L M}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hFG : f.lang = g.lang)
    (h₁ : Structure.Homomorphism act B₁ N)
    (h₂ : Structure.Homomorphism act B₂ N)
    (hLang : h₁.lang = h₂.lang)
    (hAgree : ∀ c : I, h₁ (f c) = h₂ (g c)) :
    Structure.Homomorphism act
      (amalgamStructure act f g hFG) N where
  lang := h₁.lang
  toFun := gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun
  map_rel := by
    intro n R xs hr
    change
      (∃ ls : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ ls = xs ∧ B₁.rel R ls) ∨
      (∃ rs : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ rs = xs ∧ B₂.rel R rs) at hr
    rcases hr with ⟨ls, hEq, hR⟩ | ⟨rs, hEq, hR⟩
    · have h := h₁.map_rel R ls hR
      change N.rel (act.onRel h₁.lang R)
        (gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun ∘ xs)
      have ht :
          gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun ∘ xs =
            h₁.toFun ∘ ls := by
        rw [← hEq]
        funext i
        rfl
      rw [ht]
      exact h
    · have h := h₂.map_rel R rs hR
      rw [← hLang] at h
      change N.rel (act.onRel h₁.lang R)
        (gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun ∘ xs)
      have ht :
          gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun ∘ xs =
            h₂.toFun ∘ rs := by
        rw [← hEq]
        funext i
        exact gluedCarrierMap_right f.toFun g.toFun g.injective
          h₁.toFun h₂.toFun hAgree (rs i)
      rw [ht]
      exact h
  map_func := by
    intro n F xs z hz
    rcases hz with ⟨t, ht, rfl⟩
    change
      (∃ ls : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ ls = xs ∧
          t ∈ Structure.imageSet (amalgamLeft f.toFun g.toFun)
            (B₁.func F ls)) ∨
      (∃ rs : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ rs = xs ∧
          t ∈ Structure.imageSet (amalgamRight f.toFun g.toFun)
            (B₂.func F rs)) at ht
    rcases ht with ⟨ls, hEq, ht⟩ | ⟨rs, hEq, ht⟩
    · rcases ht with ⟨a, ha, rfl⟩
      have h := h₁.map_func F ls ⟨a, ha, rfl⟩
      change gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun
          (amalgamLeft f.toFun g.toFun a) ∈
        N.func (act.onFunc h₁.lang F)
          (gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun ∘ xs)
      rw [gluedCarrierMap_left]
      have htuple :
          gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun ∘ xs =
            h₁.toFun ∘ ls := by
        rw [← hEq]
        funext i
        rfl
      rw [htuple]
      exact h
    · rcases ht with ⟨a, ha, rfl⟩
      have h := h₂.map_func F rs ⟨a, ha, rfl⟩
      rw [← hLang] at h
      change gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun
          (amalgamRight f.toFun g.toFun a) ∈
        N.func (act.onFunc h₁.lang F)
          (gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun ∘ xs)
      rw [gluedCarrierMap_right f.toFun g.toFun g.injective
        h₁.toFun h₂.toFun hAgree a]
      have htuple :
          gluedCarrierMap f.toFun g.toFun h₁.toFun h₂.toFun ∘ xs =
            h₂.toFun ∘ rs := by
        rw [← hEq]
        funext i
        exact gluedCarrierMap_right f.toFun g.toFun g.injective
          h₁.toFun h₂.toFun hAgree (rs i)
      rw [htuple]
      exact h

@[simp] theorem amalgamGluedHomomorphism_apply_left
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X}
    {B₂ : Structure L Y} {N : Structure L M}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hFG : f.lang = g.lang)
    (h₁ : Structure.Homomorphism act B₁ N)
    (h₂ : Structure.Homomorphism act B₂ N)
    (hLang : h₁.lang = h₂.lang)
    (hAgree : ∀ c : I, h₁ (f c) = h₂ (g c)) (x : X) :
    amalgamGluedHomomorphism act f g hFG h₁ h₂ hLang hAgree
      (amalgamLeft f.toFun g.toFun x) = h₁ x := rfl

theorem amalgamGluedHomomorphism_apply_right
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X}
    {B₂ : Structure L Y} {N : Structure L M}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hFG : f.lang = g.lang)
    (h₁ : Structure.Homomorphism act B₁ N)
    (h₂ : Structure.Homomorphism act B₂ N)
    (hLang : h₁.lang = h₂.lang)
    (hAgree : ∀ c : I, h₁ (f c) = h₂ (g c)) (y : Y) :
    amalgamGluedHomomorphism act f g hFG h₁ h₂ hLang hAgree
      (amalgamRight f.toFun g.toFun y) = h₂ y :=
  gluedCarrierMap_right f.toFun g.toFun g.injective
    h₁.toFun h₂.toFun hAgree y

end TreeLike
end AllThoseEPPA
