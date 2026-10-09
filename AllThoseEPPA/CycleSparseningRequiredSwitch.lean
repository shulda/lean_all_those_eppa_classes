import AllThoseEPPA.CycleSparseningDiscrepancyConsistency

/-!
# The canonical global Boolean correction for a partial automorphism

For each bad induced cycle, use the unique discrepancy required by any
source witness vertex whose base point lies on that cycle. When there is
no source vertex, use the neutral bit false. The consistency lemma proves
that this convention is independent of the chosen source witness.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- The canonical cycle-wise switch determined by a partial automorphism,
a compatible base automorphism and a chosen 0-bit off the source support. -/
noncomputable def requiredSwitch
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g) :
    Structure.BadCycleSequence B₀ E → Bool := by
  classical
  intro c
  exact if h : Nonempty (SourceWitness act B₀ E p c) then
    let w := Classical.choice h
    bitDiscrepancy act B₀ E p g hfix hcompat
      w.1 w.2.1 c w.2.2
  else false

/-- On every cycle meeting the source, the selected switch bit is precisely
the discrepancy of any prescribed source witness. -/
theorem requiredSwitch_eq_of_source
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (hsource : WitnessSetGeneric B₀ E p.source)
    (htarget : WitnessSetGeneric B₀ E p.target)
    (w : WitnessVertex B₀ E) (hw : w ∈ p.source)
    (c : Structure.BadCycleSequence B₀ E)
    (hwc : w.base B₀ E ∈ c.carrier) :
    requiredSwitch act B₀ E p g hfix hcompat c =
      bitDiscrepancy act B₀ E p g hfix hcompat
        w hw c hwc := by
  classical
  have h : Nonempty (SourceWitness act B₀ E p c) :=
    ⟨⟨w, hw, hwc⟩⟩
  unfold requiredSwitch
  simp only [dif_pos h]
  let t : SourceWitness act B₀ E p c := Classical.choice h
  exact bitDiscrepancy_eq_of_generic
    act B₀ E p g hfix hcompat hsource htarget
    t.1 w t.2.1 hw c t.2.2 hwc

/-- Flipping a Boolean bit by the discrepancy with a target gives the target. -/
theorem bitFlip_discrepancy (a b : Bool) :
    bitFlip (a != b) a = b := by
  cases a <;> cases b <;> decide

/-- The selected global correction sends the source centre bit to the
corresponding target centre bit on every bad cycle meeting the source. -/
theorem requiredSwitch_corrects_center
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (hsource : WitnessSetGeneric B₀ E p.source)
    (htarget : WitnessSetGeneric B₀ E p.target)
    (w : WitnessVertex B₀ E) (hw : w ∈ p.source)
    (c : Structure.BadCycleSequence B₀ E)
    (hwc : w.base B₀ E ∈ c.carrier)
    (htc : (p w).base B₀ E ∈ (c.transport g hfix).carrier) :
    bitFlip (requiredSwitch act B₀ E p g hfix hcompat c)
      (centerBit B₀ E w c hwc) =
      centerBit B₀ E (p w) (c.transport g hfix) htc := by
  rw [requiredSwitch_eq_of_source act B₀ E p g hfix
    hcompat hsource htarget w hw c hwc]
  change
    bitFlip
      (centerBit B₀ E w c hwc !=
        centerBit B₀ E (p w) (c.transport g hfix) htc)
      (centerBit B₀ E w c hwc) =
      centerBit B₀ E (p w) (c.transport g hfix) htc
  exact bitFlip_discrepancy _ _

end Sparsening
end AllThoseEPPA
