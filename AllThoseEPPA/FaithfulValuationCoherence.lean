import AllThoseEPPA.FaithfulLabelCoherence

/-!
# Coherence of faithful valuation transport
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- Transport of a bad-at index along a composite base automorphism agrees
with successive transport. -/
theorem badAtEquiv_comp
    (gp gq : Structure.Automorphism act B₀)
    (x : β)
    (I : BadAt act A B₀ ψ x) :
    badAtEquiv act A B₀ ψ (gq.comp gp) x I =
      badAtEquiv act A B₀ ψ gq (gp x)
        (badAtEquiv act A B₀ ψ gp x I) := by
  apply Subtype.ext
  exact
    (BadIrreducible.transport_comp
      act A B₀ ψ gq gp I.1).symm

/-- Successive valuation-function transport agrees pointwise with transport
along the composite, after the canonical equality transport of the final bad
label index. -/
theorem valuationFunctionEquiv_comp_apply [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (gp gq : Structure.Automorphism act B₀)
    (ht : p.target = q.source)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p gp)
    (hcq : BaseCompatible act A B₀ ψ q gq)
    (hss :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).source)
    (hst :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).target)
    (hcs :
      BaseCompatible act A B₀ ψ
        (q.comp p ht) (gq.comp gp))
    (x : β)
    (χ : ValuationFunction act A B₀ ψ x)
    (I : BadAt act A B₀ ψ x) :
    valuationFunctionEquiv act A B₀ ψ
        q gq hsq htq hcq (gp x)
        (valuationFunctionEquiv act A B₀ ψ
          p gp hsp htp hcp x χ)
        (badAtEquiv act A B₀ ψ gq (gp x)
          (badAtEquiv act A B₀ ψ gp x I)) =
      badLabelEquivOfEq act A B₀ ψ
          (BadIrreducible.transport_comp
            act A B₀ ψ gq gp I.1).symm
        (valuationFunctionEquiv act A B₀ ψ
          (q.comp p ht) (gq.comp gp)
          hss hst hcs x χ
          (badAtEquiv act A B₀ ψ (gq.comp gp) x I)) := by
  rw [valuationFunctionEquiv_apply_transport
    act A B₀ ψ q gq hsq htq hcq
    (gp x)
    (valuationFunctionEquiv act A B₀ ψ
      p gp hsp htp hcp x χ)
    (badAtEquiv act A B₀ ψ gp x I)]
  rw [valuationFunctionEquiv_apply_transport
    act A B₀ ψ p gp hsp htp hcp x χ I]
  rw [valuationFunctionEquiv_apply_transport
    act A B₀ ψ
    (q.comp p ht) (gq.comp gp)
    hss hst hcs x χ I]
  exact
    congrArg
      (fun e => e (χ I))
      (labelExtension_comp
        act A B₀ ψ p q gp gq ht
        hsp htp hsq htq hcp hcq
        hss hst hcs I)


/-- Valuation-function transport itself is coherent under composition. -/
theorem valuationFunctionEquiv_comp [Finite β]
    (p q : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (gp gq : Structure.Automorphism act B₀)
    (ht : p.target = q.source)
    (hsp : WitnessSetGeneric act A B₀ ψ p.source)
    (htp : WitnessSetGeneric act A B₀ ψ p.target)
    (hsq : WitnessSetGeneric act A B₀ ψ q.source)
    (htq : WitnessSetGeneric act A B₀ ψ q.target)
    (hcp : BaseCompatible act A B₀ ψ p gp)
    (hcq : BaseCompatible act A B₀ ψ q gq)
    (hss :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).source)
    (hst :
      WitnessSetGeneric act A B₀ ψ (q.comp p ht).target)
    (hcs :
      BaseCompatible act A B₀ ψ
        (q.comp p ht) (gq.comp gp))
    (x : β) :
    (valuationFunctionEquiv act A B₀ ψ
        p gp hsp htp hcp x).trans
      (valuationFunctionEquiv act A B₀ ψ
        q gq hsq htq hcq (gp x)) =
      valuationFunctionEquiv act A B₀ ψ
        (q.comp p ht) (gq.comp gp)
        hss hst hcs x := by
  apply Equiv.ext
  intro χ
  funext J
  apply Subtype.ext
  let e :=
    (badAtEquiv act A B₀ ψ gp x).trans
      (badAtEquiv act A B₀ ψ gq (gp x))
  let I : BadAt act A B₀ ψ x := e.symm J
  have hJ : e I = J := e.apply_symm_apply J
  rw [← hJ]
  have hp :=
    congrArg Subtype.val
      (valuationFunctionEquiv_comp_apply
        act A B₀ ψ p q gp gq ht
        hsp htp hsq htq hcp hcq
        hss hst hcs x χ I)
  have hp' :
      (valuationFunctionEquiv act A B₀ ψ
          q gq hsq htq hcq (gp x)
          (valuationFunctionEquiv act A B₀ ψ
            p gp hsp htp hcp x χ)
          (badAtEquiv act A B₀ ψ gq (gp x)
            (badAtEquiv act A B₀ ψ gp x I))).1 =
        (valuationFunctionEquiv act A B₀ ψ
          (q.comp p ht) (gq.comp gp)
          hss hst hcs x χ
          (badAtEquiv act A B₀ ψ (gq.comp gp) x I)).1 := by
    calc
      _ =
          (badLabelEquivOfEq act A B₀ ψ
            (BadIrreducible.transport_comp
              act A B₀ ψ gq gp I.1).symm
            (valuationFunctionEquiv act A B₀ ψ
              (q.comp p ht) (gq.comp gp)
              hss hst hcs x χ
              (badAtEquiv act A B₀ ψ
                (gq.comp gp) x I))).1 := hp
      _ =
          (valuationFunctionEquiv act A B₀ ψ
            (q.comp p ht) (gq.comp gp)
            hss hst hcs x χ
            (badAtEquiv act A B₀ ψ
              (gq.comp gp) x I)).1 :=
        badLabelEquivOfEq_apply_val
          act A B₀ ψ
          (BadIrreducible.transport_comp
            act A B₀ ψ gq gp I.1).symm
          _
  have hidx :=
    congrArg
      (fun K =>
        (valuationFunctionEquiv act A B₀ ψ
          (q.comp p ht) (gq.comp gp)
          hss hst hcs x χ K).1)
      (badAtEquiv_comp act A B₀ ψ gp gq x I)
  simpa [e] using hp'.trans hidx


end Faithful
end AllThoseEPPA
