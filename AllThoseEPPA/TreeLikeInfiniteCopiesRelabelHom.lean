import AllThoseEPPA.Relabelling
import AllThoseEPPA.Map

/-!
# Relabelling the source of a Γ-homomorphism

In the general Γ-free amalgam, the second side is relabelled
so that both interface embeddings have the same language
component. A map from the ORIGINAL second side to an ambient
target M must therefore be transported to a map from the
RELABELLED side, with adjusted language component.

The rule is h.lang * k⁻¹ for the source relabelling by k,
and the vertex map is literally unchanged. All relation
preservation and set-valued function inclusion are checked
for arbitrary arities. This will be used in the gluing
step of Lemma lem:infinitecopies.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- A Γ-homomorphism out of the structure relabelled by k,
with the same vertex map and adjusted language component. -/
def relabelSource
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (h : Homomorphism act A B) (k : Γ) :
    Homomorphism act (A.relabel act k) B where
  lang := h.lang * k⁻¹
  toFun := h.toFun
  map_rel := by
    intro n R xs hr
    have hOld : A.rel (act.onRel k⁻¹ R) xs := hr
    have hh := h.map_rel (act.onRel k⁻¹ R) xs hOld
    simpa only [Language.Action.onRel_mul] using hh
  map_func := by
    intro n F xs y hy
    have hh := h.map_func (act.onFunc k⁻¹ F) xs hy
    simpa only [Language.Action.onFunc_mul] using hh

@[simp] theorem relabelSource_lang
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (h : Homomorphism act A B) (k : Γ) :
    (h.relabelSource act k).lang = h.lang * k⁻¹ := rfl

@[simp] theorem relabelSource_apply
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (h : Homomorphism act A B) (k : Γ) (x : V) :
    (h.relabelSource act k) x = h x := rfl

end Homomorphism
end Structure
end AllThoseEPPA
