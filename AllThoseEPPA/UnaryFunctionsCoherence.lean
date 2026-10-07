import AllThoseEPPA.UnaryFunctions

/-!
# Coherence and extension for unary-function EPPA

This file continues the formalization of Proposition `prop:eppafunctions`
after the presentation-independent physical witness has been constructed.
-/

namespace AllThoseEPPA
namespace UnaryFunctions

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v} [Fintype α]
variable (act : L.Action Γ) (A : Structure L α)
variable {β : Type z} [Finite β]
variable (B₀ : Structure L.relationalReduct β)

/-- Conjugation of physical signatures is functorial in the base
automorphism. -/
theorem ValuationSignature.transport_comp
    (h g : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : ValuationSignature (L := L) x) :
    (s.transport act B₀ g).transport act B₀ h =
      s.transport act B₀ (h.comp g) := by
  apply ValuationSignature.ext
  · change h '' (g '' s.support) = (fun z => h (g z)) '' s.support
    ext b
    constructor
    · rintro ⟨c, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g a, ⟨a, ha, rfl⟩, rfl⟩
  · funext n F a
    let eh := automorphismEquiv act h
    let eg := automorphismEquiv act g
    let ec := automorphismEquiv act (h.comp g)
    have hpre : eg.symm (eh.symm a) = ec.symm a := by
      apply ec.injective
      change h (g (eg.symm (eh.symm a))) = a
      rw [show g (eg.symm (eh.symm a)) = eh.symm a by
        exact eg.apply_symm_apply (eh.symm a)]
      exact eh.apply_symm_apply a
    have hsym :
        act.onFunc g.lang⁻¹ (act.onFunc h.lang⁻¹ F) =
          act.onFunc (h.comp g).lang⁻¹ F := by
      change
        act.onFunc g.lang⁻¹ (act.onFunc h.lang⁻¹ F) =
          act.onFunc (h.lang * g.lang)⁻¹ F
      rw [mul_inv_rev]
      exact (Language.Action.onFunc_mul act g.lang⁻¹ h.lang⁻¹ F).symm
    change
      h '' (g '' s.func
        (act.onFunc g.lang⁻¹ (act.onFunc h.lang⁻¹ F))
        (eg.symm (eh.symm a))) =
        (fun z => h (g z)) ''
          s.func (act.onFunc (h.comp g).lang⁻¹ F) (ec.symm a)
    rw [hpre, hsym]
    ext b
    constructor
    · rintro ⟨c, ⟨d, hd, rfl⟩, rfl⟩
      exact ⟨d, hd, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨g d, ⟨d, hd, rfl⟩, rfl⟩

end UnaryFunctions
end AllThoseEPPA
