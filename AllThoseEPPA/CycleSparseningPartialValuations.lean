import AllThoseEPPA.CycleSparseningPartialBits

/-!
# Fibrewise correction of cycle valuations

A compatible base automorphism reindexes the valuation coordinates. The
canonical global switch then corrects those coordinates to agree with the
given partial witness automorphism, simultaneously at every point of each
source one-point closure.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Transport plus the canonical Boolean correction gives the exact valuation
function carried by the prescribed partial-automorphism image. -/
theorem correctedValuationFunction_eq_of_mem_source
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (hsource : WitnessSetGeneric B₀ E p.source)
    (htarget : WitnessSetGeneric B₀ E p.target)
    (w : WitnessVertex B₀ E) (hw : w ∈ p.source)
    (y : V) (hy : y ∈ B₀.closureAtSet (w.base B₀ E)) :
    let hy' : g y ∈ B₀.closureAtSet ((p w).base B₀ E) := by
      have h := Faithful.automorphism_maps_closureAtSet act B₀ g hy
      simpa [hcompat.2 w hw] using h
    valuationFunctionFlip B₀ E
      (transportedSwitch act B₀ E g hfix
        (requiredSwitch act B₀ E p g hfix hcompat))
      (valuationFunctionTransportEquiv act B₀ E g hfix y
        ((w.valuation B₀ E).1 ⟨y, hy⟩)) =
      ((p w).valuation B₀ E).1 ⟨g y, hy'⟩ := by
  dsimp
  let hy' : g y ∈ B₀.closureAtSet ((p w).base B₀ E) := by
    have h := Faithful.automorphism_maps_closureAtSet act B₀ g hy
    simpa [hcompat.2 w hw] using h
  funext J
  let e := badCyclesAtEquiv act B₀ E g hfix y
  let I := e.symm J
  have hJ : e I = J := e.apply_symm_apply J
  rw [← hJ]
  change
    bitFlip
      (transportedSwitch act B₀ E g hfix
        (requiredSwitch act B₀ E p g hfix hcompat) (e I).1)
      ((valuationFunctionTransportEquiv act B₀ E g hfix y
        ((w.valuation B₀ E).1 ⟨y, hy⟩)) (e I)) =
      ((p w).valuation B₀ E).1 ⟨g y, hy'⟩ (e I)
  rw [valuationFunctionTransportEquiv_apply_transport
    act B₀ E g hfix y ((w.valuation B₀ E).1 ⟨y, hy⟩) I]
  change
    bitFlip
      (transportedSwitch act B₀ E g hfix
        (requiredSwitch act B₀ E p g hfix hcompat)
        (I.1.transport g hfix))
      (((w.valuation B₀ E).1 ⟨y, hy⟩) I) =
      (((p w).valuation B₀ E).1 ⟨g y, hy'⟩)
        ⟨I.1.transport g hfix,
          (Structure.BadCycleSequence.mem_transport_carrier_iff
            I.1 g hfix y).2 I.2⟩
  rw [transportedSwitch_transport]
  exact requiredSwitch_corrects_at_closure
    act B₀ E p g hfix hcompat hsource htarget
    w hw y hy I.1 I.2 hy'
    ((Structure.BadCycleSequence.mem_transport_carrier_iff
      I.1 g hfix y).2 I.2)

end Sparsening
end AllThoseEPPA
