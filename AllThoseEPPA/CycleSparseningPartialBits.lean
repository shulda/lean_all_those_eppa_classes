import AllThoseEPPA.CycleSparseningPartialClosure

/-!
# Correcting all valuation bits in one-point closures

The canonical cycle switch is already known to correct each centre bit.
This file lifts the statement to arbitrary internal valuation points of a
source witness vertex, by applying it to the corresponding restriction
descendant.  The idea exactly parallels `FaithfulExtension`.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Centre bits are independent of equality witnesses and membership proofs. -/
theorem centerBit_congr
    {u v : WitnessVertex B₀ E}
    (huv : u = v)
    (c : Structure.BadCycleSequence B₀ E)
    (hu : u.base B₀ E ∈ c.carrier)
    (hv : v.base B₀ E ∈ c.carrier) :
    centerBit B₀ E u c hu = centerBit B₀ E v c hv := by
  subst v
  rfl

/-- The selected cycle switch corrects every valuation bit in the whole
one-point closure of any source vertex, not merely its centre. -/
theorem requiredSwitch_corrects_at_closure
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (hsource : WitnessSetGeneric B₀ E p.source)
    (htarget : WitnessSetGeneric B₀ E p.target)
    (w : WitnessVertex B₀ E) (hw : w ∈ p.source)
    (y : V) (hy : y ∈ B₀.closureAtSet (w.base B₀ E))
    (c : Structure.BadCycleSequence B₀ E)
    (hyc : y ∈ c.carrier)
    (hy' : g y ∈ B₀.closureAtSet ((p w).base B₀ E))
    (hcyc : g y ∈ (c.transport g hfix).carrier) :
    bitFlip (requiredSwitch act B₀ E p g hfix hcompat c)
      (((w.valuation B₀ E).1 ⟨y, hy⟩) ⟨c, hyc⟩) =
      (((p w).valuation B₀ E).1 ⟨g y, hy'⟩)
        ⟨c.transport g hfix, hcyc⟩ := by
  let d := restrictionVertex B₀ E w y hy
  have hdsrc : d ∈ p.source :=
    restrictionVertex_mem_source act B₀ E p w hw y hy
  have hpd :
      p d = restrictionVertex B₀ E (p w) (g y) hy' := by
    simpa [d] using
      (partialAutomorphism_restrictionVertex
        act B₀ E p g hcompat w hw y hy)
  have hdc : d.base B₀ E ∈ c.carrier := hyc
  have hpdc : (p d).base B₀ E ∈ (c.transport g hfix).carrier := by
    rw [← hcompat.2 d hdsrc]
    exact (Structure.BadCycleSequence.mem_transport_carrier_iff
      c g hfix y).2 hyc
  have hsourceBit :
      centerBit B₀ E d c hdc =
        ((w.valuation B₀ E).1 ⟨y, hy⟩) ⟨c, hyc⟩ :=
    centerBit_restrictionVertex B₀ E w y hy c hyc
  have htargetBit :
      centerBit B₀ E (p d) (c.transport g hfix) hpdc =
        ((p w).valuation B₀ E).1 ⟨g y, hy'⟩
          ⟨c.transport g hfix, hcyc⟩ := by
    calc
      centerBit B₀ E (p d) (c.transport g hfix) hpdc =
          centerBit B₀ E
            (restrictionVertex B₀ E (p w) (g y) hy')
            (c.transport g hfix) hcyc :=
        centerBit_congr B₀ E hpd (c.transport g hfix) hpdc hcyc
      _ = ((p w).valuation B₀ E).1 ⟨g y, hy'⟩
          ⟨c.transport g hfix, hcyc⟩ :=
        centerBit_restrictionVertex B₀ E
          (p w) (g y) hy' (c.transport g hfix) hcyc
  calc
    bitFlip (requiredSwitch act B₀ E p g hfix hcompat c)
        (((w.valuation B₀ E).1 ⟨y, hy⟩) ⟨c, hyc⟩) =
      bitFlip (requiredSwitch act B₀ E p g hfix hcompat c)
        (centerBit B₀ E d c hdc) :=
      congrArg _ hsourceBit.symm
    _ = centerBit B₀ E (p d) (c.transport g hfix) hpdc :=
      requiredSwitch_corrects_center act B₀ E
        p g hfix hcompat hsource htarget d hdsrc c hdc hpdc
    _ = ((p w).valuation B₀ E).1 ⟨g y, hy'⟩
          ⟨c.transport g hfix, hcyc⟩ := htargetBit

end Sparsening
end AllThoseEPPA
