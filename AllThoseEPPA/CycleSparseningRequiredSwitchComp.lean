import AllThoseEPPA.CycleSparseningDiscrepancyCocycle

/-!
# Composition of canonical cycle-switch assignments

The canonical correction for a composite partial automorphism is the
pointwise XOR of the first correction and the second correction transported
back to the source bad-cycle indexing.  The result follows by splitting
on whether a bad cycle meets the first source. Off that support all three
corrections are zero.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- The Boolean correction used in the sparsening lift respects
composition of compatible partial automorphisms. -/
theorem requiredSwitch_comp
    (p q : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (ht : p.target = q.source)
    (hcp : BaseCompatible act B₀ E p gp)
    (hcq : BaseCompatible act B₀ E q gq)
    (hcomp : BaseCompatible act B₀ E (q.comp p ht) (gq.comp gp))
    (hsp : WitnessSetGeneric B₀ E p.source)
    (htp : WitnessSetGeneric B₀ E p.target)
    (hsq : WitnessSetGeneric B₀ E q.source)
    (htq : WitnessSetGeneric B₀ E q.target)
    (hsrc : WitnessSetGeneric B₀ E (q.comp p ht).source)
    (htgt : WitnessSetGeneric B₀ E (q.comp p ht).target) :
    requiredSwitch act B₀ E (q.comp p ht) (gq.comp gp) hfix hcomp =
      switchSum B₀ E
        (requiredSwitch act B₀ E p gp hfix hcp)
        (fun c => requiredSwitch act B₀ E q gq hfix hcq
          (c.transport gp hfix)) := by
  classical
  funext c
  change
    requiredSwitch act B₀ E (q.comp p ht) (gq.comp gp)
      hfix hcomp c =
      (requiredSwitch act B₀ E p gp hfix hcp c !=
       requiredSwitch act B₀ E q gq hfix hcq
         (c.transport gp hfix))
  by_cases h : Nonempty (SourceWitness act B₀ E p c)
  · rcases h with ⟨⟨x, hx, hxc⟩⟩
    have hxr : x ∈ (q.comp p ht).source :=
      (mem_comp_source_iff act B₀ E p q ht x).2 hx
    have hpx : p x ∈ q.source := by
      rw [← ht]
      exact p.map_source hx
    have hpxc : (p x).base B₀ E ∈ (c.transport gp hfix).carrier := by
      rw [← hcp.2 x hx]
      exact (Structure.BadCycleSequence.mem_transport_carrier_iff
        c gp hfix (x.base B₀ E)).2 hxc
    rw [requiredSwitch_eq_of_source
          act B₀ E (q.comp p ht) (gq.comp gp) hfix
          hcomp hsrc htgt x hxr c hxc,
        requiredSwitch_eq_of_source
          act B₀ E p gp hfix
          hcp hsp htp x hx c hxc,
        requiredSwitch_eq_of_source
          act B₀ E q gq hfix
          hcq hsq htq (p x) hpx (c.transport gp hfix) hpxc]
    exact bitDiscrepancy_comp_of_source
      act B₀ E p q gp gq hfix ht hcp hcq hcomp x hx c hxc
  · have hr : ¬ Nonempty
        (SourceWitness act B₀ E (q.comp p ht) c) := by
      intro hw
      exact h ((sourceWitness_comp_nonempty_iff
        act B₀ E p q ht c).1 hw)
    have hq : ¬ Nonempty
        (SourceWitness act B₀ E q (c.transport gp hfix)) := by
      intro hw
      exact h ((sourceWitness_transport_nonempty_iff
        act B₀ E p q gp hfix ht hcp c).1 hw)
    rw [requiredSwitch_eq_false_of_no_source
          act B₀ E (q.comp p ht) (gq.comp gp) hfix hcomp c hr,
        requiredSwitch_eq_false_of_no_source
          act B₀ E p gp hfix hcp c h,
        requiredSwitch_eq_false_of_no_source
          act B₀ E q gq hfix hcq (c.transport gp hfix) hq]
    rfl

end Sparsening
end AllThoseEPPA
