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
  let I : BadAt act A B₀ ψ x :=
    (badAtEquiv act A B₀ ψ gp x).symm
      ((badAtEquiv act A B₀ ψ gq (gp x)).symm J)
  have hJ :
      badAtEquiv act A B₀ ψ gq (gp x)
          (badAtEquiv act A B₀ ψ gp x I) = J := by
    simp [I]
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
  exact hp'.trans hidx


/-- Closure-point transport is coherent under composition of base
automorphisms. -/
theorem closureTransportEquiv_comp
    (gp gq : Structure.Automorphism act B₀)
    (x : β)
    (y : B₀.closureAtSet x) :
    closureTransportEquiv act B₀ (gq.comp gp) x y =
      closureTransportEquiv act B₀ gq (gp x)
        (closureTransportEquiv act B₀ gp x y) := by
  apply Subtype.ext
  rfl

/-- Successive valuation-assignment transport agrees at every transported
closure point with transport along the composite. -/
theorem valuationAssignmentEquiv_comp_apply [Finite β]
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
    (V : ValuationAssignment act A B₀ ψ x)
    (y : B₀.closureAtSet x) :
    valuationAssignmentEquiv act A B₀ ψ
        q gq hsq htq hcq (gp x)
        (valuationAssignmentEquiv act A B₀ ψ
          p gp hsp htp hcp x V)
        (closureTransportEquiv act B₀ gq (gp x)
          (closureTransportEquiv act B₀ gp x y)) =
      valuationAssignmentEquiv act A B₀ ψ
        (q.comp p ht) (gq.comp gp)
        hss hst hcs x V
        (closureTransportEquiv act B₀
          (gq.comp gp) x y) := by
  rw [valuationAssignmentEquiv_apply_transport
    act A B₀ ψ q gq hsq htq hcq
    (gp x)
    (valuationAssignmentEquiv act A B₀ ψ
      p gp hsp htp hcp x V)
    (closureTransportEquiv act B₀ gp x y)]
  rw [valuationAssignmentEquiv_apply_transport
    act A B₀ ψ p gp hsp htp hcp x V y]
  rw [valuationAssignmentEquiv_apply_transport
    act A B₀ ψ
    (q.comp p ht) (gq.comp gp)
    hss hst hcs x V y]
  exact
    congrArg
      (fun e => e (V y))
      (valuationFunctionEquiv_comp
        act A B₀ ψ p q gp gq ht
        hsp htp hsq htq hcp hcq
        hss hst hcs y.1)


/-- Valuation-assignment transport is coherent under composition. -/
theorem valuationAssignmentEquiv_comp [Finite β]
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
    (valuationAssignmentEquiv act A B₀ ψ
        p gp hsp htp hcp x).trans
      (valuationAssignmentEquiv act A B₀ ψ
        q gq hsq htq hcq (gp x)) =
      valuationAssignmentEquiv act A B₀ ψ
        (q.comp p ht) (gq.comp gp)
        hss hst hcs x := by
  apply Equiv.ext
  intro V
  funext z
  let y : B₀.closureAtSet x :=
    (closureTransportEquiv act B₀ gp x).symm
      ((closureTransportEquiv act B₀ gq (gp x)).symm z)
  have hz :
      closureTransportEquiv act B₀ gq (gp x)
          (closureTransportEquiv act B₀ gp x y) = z := by
    simp [y]
  rw [← hz]
  let tSeq :=
    closureTransportEquiv act B₀ gq (gp x)
      (closureTransportEquiv act B₀ gp x y)
  let tComp :=
    closureTransportEquiv act B₀ (gq.comp gp) x y
  let W :=
    valuationAssignmentEquiv act A B₀ ψ
      (q.comp p ht) (gq.comp gp)
      hss hst hcs x V
  have htPoint : tComp = tSeq := by
    exact closureTransportEquiv_comp act B₀ gp gq x y
  have hdep : HEq (W tComp) (W tSeq) := by
    have hsigma :
        (⟨tComp, W tComp⟩ :
          Σ t : B₀.closureAtSet ((gq.comp gp) x),
            ValuationFunction act A B₀ ψ t.1) =
        ⟨tSeq, W tSeq⟩ :=
      congrArg
        (fun t =>
          (⟨t, W t⟩ :
            Σ s : B₀.closureAtSet ((gq.comp gp) x),
              ValuationFunction act A B₀ ψ s.1))
        htPoint
    exact (Sigma.mk.inj_iff.mp hsigma).2
  have hp :=
    valuationAssignmentEquiv_comp_apply
      act A B₀ ψ p q gp gq ht
      hsp htp hsq htq hcp hcq
      hss hst hcs x V y
  change
    valuationAssignmentEquiv act A B₀ ψ
        q gq hsq htq hcq (gp x)
        (valuationAssignmentEquiv act A B₀ ψ
          p gp hsp htp hcp x V) tSeq =
      W tSeq
  have hpheq :
      HEq
        (valuationAssignmentEquiv act A B₀ ψ
          q gq hsq htq hcq (gp x)
          (valuationAssignmentEquiv act A B₀ ψ
            p gp hsp htp hcp x V) tSeq)
        (W tComp) := by
    exact heq_of_eq hp
  exact eq_of_heq (hpheq.trans hdep)

/-- Transport of complete valuation structures is coherent under composition. -/
theorem ValuationStructure.transport_comp [Finite β]
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
    {x : β}
    (V : ValuationStructure act A B₀ ψ x) :
    ValuationStructure.transport act A B₀ ψ
        q gq hsq htq hcq
        (ValuationStructure.transport act A B₀ ψ
          p gp hsp htp hcp V) =
      ValuationStructure.transport act A B₀ ψ
        (q.comp p ht) (gq.comp gp)
        hss hst hcs V := by
  apply Subtype.ext
  change
    valuationAssignmentEquiv act A B₀ ψ
        q gq hsq htq hcq (gp x)
        (valuationAssignmentEquiv act A B₀ ψ
          p gp hsp htp hcp x V.1) =
      valuationAssignmentEquiv act A B₀ ψ
        (q.comp p ht) (gq.comp gp)
        hss hst hcs x V.1
  exact
    congrArg
      (fun e => e V.1)
      (valuationAssignmentEquiv_comp
        act A B₀ ψ p q gp gq ht
        hsp htp hsq htq hcp hcq
        hss hst hcs x)


end Faithful
end AllThoseEPPA
