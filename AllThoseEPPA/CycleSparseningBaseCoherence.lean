import AllThoseEPPA.CycleSparseningCanonicalLift
import AllThoseEPPA.CycleSparseningTransportComposition

/-!
# Coherent composition of pure base reindexing lifts

The cycle-sparsening witness transports entire one-point closure assignments
along automorphisms of B₀. Because the Boolean fibres carry the identity
equivalence, composition is simply functoriality of the bad-cycle index and
the closure index. Unlike the faithful construction, no label-extension
composition is necessary.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Bad-cycle index equivalences commute with successive base transports. -/
theorem badCyclesAtEquiv_comp
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (x : V) (I : BadCyclesAt B₀ E x) :
    badCyclesAtEquiv act B₀ E (gq.comp gp) hfix x I =
      badCyclesAtEquiv act B₀ E gq hfix (gp x)
        (badCyclesAtEquiv act B₀ E gp hfix x I) := by
  apply Subtype.ext
  exact
    (Structure.BadCycleSequence.transport_comp I.1 gq gp hfix).symm

/-- Boolean valuation function transport is strictly functorial. -/
theorem valuationFunctionTransport_comp
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (x : V) (χ : ValuationFunction B₀ E x) :
    valuationFunctionTransportEquiv act B₀ E gq hfix (gp x)
        (valuationFunctionTransportEquiv act B₀ E gp hfix x χ) =
      valuationFunctionTransportEquiv act B₀ E
        (gq.comp gp) hfix x χ := by
  funext J
  let e₀ := badCyclesAtEquiv act B₀ E gp hfix x
  let e₁ := badCyclesAtEquiv act B₀ E gq hfix (gp x)
  let I := e₀.symm (e₁.symm J)
  have hJ : e₁ (e₀ I) = J := by
    simp [I]
  rw [← hJ]
  rw [valuationFunctionTransportEquiv_apply_transport
    act B₀ E gq hfix (gp x)
    (valuationFunctionTransportEquiv act B₀ E gp hfix x χ) (e₀ I)]
  rw [valuationFunctionTransportEquiv_apply_transport
    act B₀ E gp hfix x χ I]
  rw [← badCyclesAtEquiv_comp act B₀ E gp gq hfix x I]
  exact (valuationFunctionTransportEquiv_apply_transport
    act B₀ E (gq.comp gp) hfix x χ I).symm

/-- Closure-point transport is functorial, reusing the faithful construction. -/
theorem closureTransport_comp
    (gp gq : Structure.Automorphism act B₀)
    (x : V) (y : B₀.closureAtSet x) :
    Faithful.closureTransportEquiv act B₀ (gq.comp gp) x y =
      Faithful.closureTransportEquiv act B₀ gq (gp x)
        (Faithful.closureTransportEquiv act B₀ gp x y) := by
  apply Subtype.ext
  rfl

/-- Transporting the whole valuation assignment along two base automorphisms
equals transporting it directly by their composite. -/
theorem valuationAssignmentTransport_comp
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (x : V) (W : ValuationAssignment B₀ E x) :
    valuationAssignmentEquiv act B₀ E gq hfix (gp x)
        (valuationAssignmentEquiv act B₀ E gp hfix x W) =
      valuationAssignmentEquiv act B₀ E (gq.comp gp) hfix x W := by
  funext z
  let e₀ := Faithful.closureTransportEquiv act B₀ gp x
  let e₁ := Faithful.closureTransportEquiv act B₀ gq (gp x)
  let y := e₀.symm (e₁.symm z)
  have hz : e₁ (e₀ y) = z := by
    simp [y]
  rw [← hz]
  let ec := Faithful.closureTransportEquiv act B₀ (gq.comp gp) x
  let tSeq := e₁ (e₀ y)
  let tComp := ec y
  let T := valuationAssignmentEquiv act B₀ E (gq.comp gp) hfix x W
  have hpoint : tComp = tSeq :=
    closureTransport_comp act B₀ gp gq x y
  have hdep : HEq (T tComp) (T tSeq) := by
    have hsigma :
        (⟨tComp, T tComp⟩ :
          Σ t : B₀.closureAtSet ((gq.comp gp) x),
            ValuationFunction B₀ E t.1) =
        ⟨tSeq, T tSeq⟩ :=
      congrArg
        (fun t =>
          (⟨t, T t⟩ :
            Σ s : B₀.closureAtSet ((gq.comp gp) x),
              ValuationFunction B₀ E s.1))
        hpoint
    exact (Sigma.mk.inj_iff.mp hsigma).2
  have hl :
      valuationAssignmentEquiv act B₀ E gq hfix (gp x)
          (valuationAssignmentEquiv act B₀ E gp hfix x W) tSeq =
      valuationFunctionTransportEquiv act B₀ E gq hfix (gp y.1)
        (valuationFunctionTransportEquiv act B₀ E gp hfix y.1 (W y)) := by
    rw [valuationAssignmentEquiv_apply_transport act B₀ E gq hfix
      (gp x) (valuationAssignmentEquiv act B₀ E gp hfix x W) (e₀ y)]
    rw [valuationAssignmentEquiv_apply_transport act B₀ E gp hfix x W y]
  have hr :=
    valuationAssignmentEquiv_apply_transport
      act B₀ E (gq.comp gp) hfix x W y
  have hh :
      HEq
        (valuationAssignmentEquiv act B₀ E gq hfix (gp x)
          (valuationAssignmentEquiv act B₀ E gp hfix x W) tSeq)
        (T tComp) := by
    exact heq_of_eq
      (hl.trans
        ((valuationFunctionTransport_comp
          act B₀ E gp gq hfix y.1 (W y)).trans hr.symm))
  exact eq_of_heq (hh.trans hdep)

/-- Transport of complete valuation structures composes strictly. -/
theorem ValuationStructure.transport_comp
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    {x : V} (W : ValuationStructure B₀ E x) :
    (W.transport act B₀ E gp hfix).transport act B₀ E gq hfix =
      W.transport act B₀ E (gq.comp gp) hfix := by
  apply Subtype.ext
  exact valuationAssignmentTransport_comp act B₀ E gp gq hfix x W.1

/-- Consequently, base transport on witness vertices composes strictly. -/
theorem WitnessVertex.transport_comp
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (w : WitnessVertex B₀ E) :
    (w.transport act B₀ E gp hfix).transport act B₀ E gq hfix =
      w.transport act B₀ E (gq.comp gp) hfix := by
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  exact heq_of_eq
    (ValuationStructure.transport_comp act B₀ E gp gq hfix w.2)

/-- The canonical lifts of base automorphisms respect composition exactly. -/
theorem baseAutomorphismLift_comp [Finite V]
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E) :
    baseAutomorphismLift act B₀ E (gq.comp gp) hfix =
      (baseAutomorphismLift act B₀ E gq hfix).comp
        (baseAutomorphismLift act B₀ E gp hfix) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro w
    change w.transport act B₀ E (gq.comp gp) hfix =
      (w.transport act B₀ E gp hfix).transport act B₀ E gq hfix
    exact (WitnessVertex.transport_comp act B₀ E gp gq hfix w).symm

end Sparsening
end AllThoseEPPA
