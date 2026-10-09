import AllThoseEPPA.CycleSparseningTransportComposition
import AllThoseEPPA.CycleSparseningPartialSwitch

/-!
# Supports of the canonical Boolean switch under composition

A coherent pair of partial automorphisms has matching target and source.
Consequently the bad cycles met by the first source are transported exactly
to the bad cycles met by the second source.  The canonical correction takes
the neutral bit off this support.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- A composable partial automorphism has the same source as its
first factor. -/
theorem mem_comp_source_iff
    (p q : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (ht : p.target = q.source)
    (x : WitnessVertex B₀ E) :
    x ∈ (q.comp p ht).source ↔ x ∈ p.source := by
  change x ∈ (p.toPartialEquiv.trans' q.toPartialEquiv ht).source ↔
    x ∈ p.toPartialEquiv.source
  simp [PartialEquiv.trans']

/-- A bad cycle meets the source of a composition exactly when it meets
the source of the first factor. -/
theorem sourceWitness_comp_nonempty_iff
    (p q : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (ht : p.target = q.source)
    (c : Structure.BadCycleSequence B₀ E) :
    Nonempty (SourceWitness act B₀ E (q.comp p ht) c) ↔
      Nonempty (SourceWitness act B₀ E p c) := by
  constructor
  · rintro ⟨⟨x, hx, hxc⟩⟩
    exact ⟨⟨x, (mem_comp_source_iff act B₀ E p q ht x).1 hx,
      hxc⟩⟩
  · rintro ⟨⟨x, hx, hxc⟩⟩
    exact ⟨⟨x, (mem_comp_source_iff act B₀ E p q ht x).2 hx,
      hxc⟩⟩

/-- The second source meets the transported cycle exactly when the
first source meets the original cycle. -/
theorem sourceWitness_transport_nonempty_iff
    (p q : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (gp : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (ht : p.target = q.source)
    (hcompat : BaseCompatible act B₀ E p gp)
    (c : Structure.BadCycleSequence B₀ E) :
    Nonempty (SourceWitness act B₀ E q (c.transport gp hfix)) ↔
      Nonempty (SourceWitness act B₀ E p c) := by
  constructor
  · rintro ⟨⟨z, hz, hzc⟩⟩
    have hzt : z ∈ p.target := by
      rw [ht]
      exact hz
    let x : WitnessVertex B₀ E := p.toPartialEquiv.symm z
    have hx : x ∈ p.source :=
      p.toPartialEquiv.symm.map_source hzt
    have hpx : p x = z := p.right_inv hzt
    have hcycle :
        gp (x.base B₀ E) ∈ (c.transport gp hfix).carrier := by
      rw [hcompat.2 x hx, hpx]
      exact hzc
    have hxc : x.base B₀ E ∈ c.carrier :=
      (Structure.BadCycleSequence.mem_transport_carrier_iff
        c gp hfix (x.base B₀ E)).1 hcycle
    exact ⟨⟨x, hx, hxc⟩⟩
  · rintro ⟨⟨x, hx, hxc⟩⟩
    have hpx : p x ∈ q.source := by
      rw [← ht]
      exact p.map_source hx
    have htgt :
        (p x).base B₀ E ∈ (c.transport gp hfix).carrier := by
      rw [← hcompat.2 x hx]
      exact (Structure.BadCycleSequence.mem_transport_carrier_iff
        c gp hfix (x.base B₀ E)).2 hxc
    exact ⟨⟨p x, hpx, htgt⟩⟩

/-- The canonical correction is zero on cycles disjoint from the source. -/
theorem requiredSwitch_eq_false_of_no_source
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (c : Structure.BadCycleSequence B₀ E)
    (h : ¬ Nonempty (SourceWitness act B₀ E p c)) :
    requiredSwitch act B₀ E p g hfix hcompat c = false := by
  simp [requiredSwitch, h]

/-- Three Boolean values satisfy the cocycle identity for XOR
discrepancies. -/
theorem bool_discrepancy_cocycle (a b c : Bool) :
    (a != c) = ((a != b) != (b != c)) := by
  cases a <;> cases b <;> cases c <;> decide

end Sparsening
end AllThoseEPPA
