import AllThoseEPPA.CycleSparseningPartialSwitch

/-!
# Consistency of cycle-wise discrepancies

For a generic partial automorphism compatible with a base automorphism, all
source witness vertices lying over a fixed bad cycle determine the same
Boolean correction. This is the central well-definedness fact for the
global switch required by the extension lemma.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- All source vertices meeting the same bad cycle prescribe the same
flip bit. No finiteness or choice is needed for this consistency result. -/
theorem bitDiscrepancy_eq_of_generic
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (hsource : WitnessSetGeneric B₀ E p.source)
    (htarget : WitnessSetGeneric B₀ E p.target)
    (w z : WitnessVertex B₀ E)
    (hw : w ∈ p.source) (hz : z ∈ p.source)
    (c : Structure.BadCycleSequence B₀ E)
    (hwc : w.base B₀ E ∈ c.carrier)
    (hzc : z.base B₀ E ∈ c.carrier) :
    bitDiscrepancy act B₀ E p g hfix hcompat w hw c hwc =
      bitDiscrepancy act B₀ E p g hfix hcompat z hz c hzc := by
  by_cases hbase : w.base B₀ E = z.base B₀ E
  · have heq : w = z :=
      projection_injOn_of_generic B₀ E p.source hsource
        hw hz hbase
    subst z
    rfl
  · have hsw :
        AreGeneric B₀ E (centerValuationPoint B₀ E w)
          (centerValuationPoint B₀ E z) :=
      centerValuationPoints_generic_of_source B₀ E p hsource w z hw hz
    have htw : p w ∈ p.target := p.map_source hw
    have htz : p z ∈ p.target := p.map_source hz
    have htg :
        AreGeneric B₀ E
          (centerValuationPoint B₀ E (p w))
          (centerValuationPoint B₀ E (p z)) :=
      htarget ⟨p w, htw⟩ ⟨p z, htz⟩
        (centerPoint B₀ E (p w)) (centerPoint B₀ E (p z))
    have htbase : (p w).base B₀ E ≠ (p z).base B₀ E := by
      rw [← hcompat.2 w hw, ← hcompat.2 z hz]
      intro heq
      exact hbase (g.toEquiv.injective heq)
    have hwct :
        (p w).base B₀ E ∈ (c.transport g hfix).carrier := by
      rw [← hcompat.2 w hw]
      exact (Structure.BadCycleSequence.mem_transport_carrier_iff
        c g hfix (w.base B₀ E)).2 hwc
    have hzct :
        (p z).base B₀ E ∈ (c.transport g hfix).carrier := by
      rw [← hcompat.2 z hz]
      exact (Structure.BadCycleSequence.mem_transport_carrier_iff
        c g hfix (z.base B₀ E)).2 hzc
    have hsourceParity :=
      generic_centerBits_eq_iff_nonWrap B₀ E
        w z c hwc hzc hbase hsw
    have htargetParity :=
      generic_centerBits_eq_iff_nonWrap B₀ E
        (p w) (p z) (c.transport g hfix)
        hwct hzct htbase htg
    have hnonwrap :
        c.NonWrapPair (w.base B₀ E) (z.base B₀ E) ↔
          (c.transport g hfix).NonWrapPair
            ((p w).base B₀ E) ((p z).base B₀ E) := by
      have hh := (Structure.BadCycleSequence.nonWrapPair_transport_iff
        c g hfix (w.base B₀ E) (z.base B₀ E)).symm
      simpa only [hcompat.2 w hw, hcompat.2 z hz] using hh
    have hparity :
        (centerBit B₀ E w c hwc = centerBit B₀ E z c hzc) ↔
          (centerBit B₀ E (p w) (c.transport g hfix) hwct =
            centerBit B₀ E (p z) (c.transport g hfix) hzct) :=
      hsourceParity.trans (hnonwrap.trans htargetParity.symm)
    change
      (centerBit B₀ E w c hwc !=
        centerBit B₀ E (p w) (c.transport g hfix) hwct) =
      (centerBit B₀ E z c hzc !=
        centerBit B₀ E (p z) (c.transport g hfix) hzct)
    exact bool_discrepancy_eq_of_parity _ _ _ _ hparity

end Sparsening
end AllThoseEPPA
