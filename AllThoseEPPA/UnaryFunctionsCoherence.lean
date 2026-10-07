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


/-- Functoriality descends to realised physical valuations. -/
theorem PhysicalValuation.transport_comp
    (h g : Structure.Automorphism act.relationalReduct B₀)
    {x : β} (s : PhysicalValuation act A B₀ x) :
    PhysicalValuation.transport act A B₀ h
        (PhysicalValuation.transport act A B₀ g s) =
      PhysicalValuation.transport act A B₀ (h.comp g) s := by
  apply Subtype.ext
  exact ValuationSignature.transport_comp act B₀ h g s.1

/-- Transport of whole witness vertices is functorial. -/
theorem PhysicalWitnessVertex.transport_comp
    (h g : Structure.Automorphism act.relationalReduct B₀)
    (w : PhysicalWitnessVertex act A B₀) :
    PhysicalWitnessVertex.transport act A B₀ h
        (PhysicalWitnessVertex.transport act A B₀ g w) =
      PhysicalWitnessVertex.transport act A B₀ (h.comp g) w := by
  apply Sigma.ext rfl
  exact heq_of_eq
    (PhysicalValuation.transport_comp act A B₀ h g w.2)

/-- Lifting base automorphisms to the unary witness preserves composition. -/
theorem physicalWitnessAutomorphism_comp
    (hA : A.HasFiniteRelabelOrbit act)
    (h g : Structure.Automorphism act.relationalReduct B₀) :
    physicalWitnessAutomorphism act A B₀ hA (h.comp g) =
      (physicalWitnessAutomorphism act A B₀ hA h).comp
        (physicalWitnessAutomorphism act A B₀ hA g) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro w
    change
      PhysicalWitnessVertex.transport act A B₀ (h.comp g) w =
        PhysicalWitnessVertex.transport act A B₀ h
          (PhysicalWitnessVertex.transport act A B₀ g w)
    exact (PhysicalWitnessVertex.transport_comp act A B₀ h g w).symm

end UnaryFunctions
end AllThoseEPPA
