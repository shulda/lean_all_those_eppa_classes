import AllThoseEPPA.CycleSparseningWitnessTransport
import AllThoseEPPA.CycleSparseningSwitchWitness

/-!
# Equivariance of Boolean switches under transport of bad cycles

The automorphism group of the base permutes the coordinates of the Boolean
switch space. This provides the semidirect-product law needed for coherence.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- A base automorphism acts on switch assignments by inverse image
of the indexed bad-cycle permutation. -/
noncomputable def transportedSwitch
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s : Structure.BadCycleSequence B₀ E → Bool) :
    Structure.BadCycleSequence B₀ E → Bool :=
  fun c => s ((Structure.BadCycleSequence.transportEquiv g hfix).symm c)

theorem transportedSwitch_transport
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s : Structure.BadCycleSequence B₀ E → Bool)
    (c : Structure.BadCycleSequence B₀ E) :
    transportedSwitch act B₀ E g hfix s (c.transport g hfix) = s c := by
  change s ((c.transport g hfix).transport g.symm hfix) = s c
  rw [Structure.BadCycleSequence.transport_symm_transport]

/-- Reindexing a valuation after a global Boolean switch equals
reindexing first, then switching the transported bad-cycle coordinates. -/
theorem valuationFunctionTransport_flip
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s : Structure.BadCycleSequence B₀ E → Bool)
    (x : V) (χ : ValuationFunction B₀ E x) :
    valuationFunctionTransportEquiv act B₀ E g hfix x
        (valuationFunctionFlip B₀ E s χ) =
      valuationFunctionFlip B₀ E
        (transportedSwitch act B₀ E g hfix s)
        (valuationFunctionTransportEquiv act B₀ E g hfix x χ) := by
  funext J
  let e := badCyclesAtEquiv act B₀ E g hfix x
  let I := e.symm J
  have hJ : e I = J := e.apply_symm_apply J
  rw [← hJ]
  have hl :=
    valuationFunctionTransportEquiv_apply_transport
      act B₀ E g hfix x (valuationFunctionFlip B₀ E s χ) I
  have hr :=
    valuationFunctionTransportEquiv_apply_transport
      act B₀ E g hfix x χ I
  change
    (valuationFunctionTransportEquiv act B₀ E g hfix x
        (valuationFunctionFlip B₀ E s χ)) (e I) =
      bitFlip (transportedSwitch act B₀ E g hfix s (e I).1)
        ((valuationFunctionTransportEquiv act B₀ E g hfix x χ) (e I))
  rw [hl, hr]
  change bitFlip (s I.1) (χ I) =
    bitFlip (transportedSwitch act B₀ E g hfix s
      (I.1.transport g hfix)) (χ I)
  rw [transportedSwitch_transport]

/-- The same equivariance identity on the dependent pairs of
base vertices and cycle valuation functions. -/
theorem valuationPointTransport_flip
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s : Structure.BadCycleSequence B₀ E → Bool)
    (p : ValuationPoint B₀ E) :
    valuationPointTransport act B₀ E g hfix
        (valuationPointFlip B₀ E s p) =
      valuationPointFlip B₀ E
        (transportedSwitch act B₀ E g hfix s)
        (valuationPointTransport act B₀ E g hfix p) := by
  rcases p with ⟨x, χ⟩
  let s' := transportedSwitch act B₀ E g hfix s
  have hh := valuationFunctionTransport_flip act B₀ E g hfix s x χ
  change
    (⟨g x, valuationFunctionTransportEquiv act B₀ E g hfix x
        (valuationFunctionFlip B₀ E s χ)⟩ : ValuationPoint B₀ E) =
      ⟨g x, valuationFunctionFlip B₀ E s'
        (valuationFunctionTransportEquiv act B₀ E g hfix x χ)⟩
  exact congrArg
    (fun f : ValuationFunction B₀ E (g x) =>
      (⟨g x, f⟩ : ValuationPoint B₀ E)) hh

/-- Global switching and base transport commute up to the corresponding
transport of the global switch assignment. -/
theorem ValuationStructure.transport_flip
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s : Structure.BadCycleSequence B₀ E → Bool)
    {x : V} (W : ValuationStructure B₀ E x) :
    ValuationStructure.transport act B₀ E g hfix (W.flip B₀ E s) =
      (ValuationStructure.transport act B₀ E g hfix W).flip B₀ E
        (transportedSwitch act B₀ E g hfix s) := by
  apply Subtype.ext
  funext z
  let e := Faithful.closureTransportEquiv act B₀ g x
  let y := e.symm z
  have hy : e y = z := e.apply_symm_apply z
  rw [← hy]
  change
    valuationAssignmentEquiv act B₀ E g hfix x
        (W.flip B₀ E s).1 (e y) =
      valuationFunctionFlip B₀ E
        (transportedSwitch act B₀ E g hfix s)
        (valuationAssignmentEquiv act B₀ E g hfix x W.1 (e y))
  rw [valuationAssignmentEquiv_apply_transport
    act B₀ E g hfix x (W.flip B₀ E s).1 y]
  rw [valuationAssignmentEquiv_apply_transport
    act B₀ E g hfix x W.1 y]
  exact valuationFunctionTransport_flip act B₀ E g hfix s y.1 (W.1 y)

end Sparsening
end AllThoseEPPA
