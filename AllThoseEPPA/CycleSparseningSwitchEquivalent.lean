import AllThoseEPPA.CycleSparseningSwitchSupport

/-!
# Canonical cycle corrections depend only on partial isomorphisms

The canonical switch is independent of the concrete representation of a
partial automorphism, provided its language component, source and action
on the source agree. This is the equivalence axiom of coherent EPPA.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Pointwise bit discrepancies depend only on the source vertex and
its prescribed target, not on the chosen equivalent partial map. -/
theorem bitDiscrepancy_eq_of_equivalent
    (p q : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompatP : BaseCompatible act B₀ E p g)
    (hcompatQ : BaseCompatible act B₀ E q g)
    (hpq : Structure.PartialIsomorphism.Equivalent p q)
    (x : WitnessVertex B₀ E)
    (hxp : x ∈ p.source) (hxq : x ∈ q.source)
    (c : Structure.BadCycleSequence B₀ E)
    (hxc : x.base B₀ E ∈ c.carrier) :
    bitDiscrepancy act B₀ E p g hfix hcompatP x hxp c hxc =
      bitDiscrepancy act B₀ E q g hfix hcompatQ x hxq c hxc := by
  have heq : p x = q x := hpq.2.2 hxp
  unfold bitDiscrepancy
  rw [heq]

/-- Equivalent partial automorphisms induce literally identical canonical
global Boolean switch assignments when the base automorphism is fixed. -/
theorem requiredSwitch_eq_of_equivalent
    (p q : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompatP : BaseCompatible act B₀ E p g)
    (hcompatQ : BaseCompatible act B₀ E q g)
    (hsourceP : WitnessSetGeneric B₀ E p.source)
    (htargetP : WitnessSetGeneric B₀ E p.target)
    (hsourceQ : WitnessSetGeneric B₀ E q.source)
    (htargetQ : WitnessSetGeneric B₀ E q.target)
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    requiredSwitch act B₀ E p g hfix hcompatP =
      requiredSwitch act B₀ E q g hfix hcompatQ := by
  funext c
  have hsrc : p.source = q.source := hpq.2.1
  by_cases h : Nonempty (SourceWitness act B₀ E p c)
  · rcases h with ⟨⟨x, hx, hxc⟩⟩
    have hxq : x ∈ q.source := by
      rw [← hsrc]
      exact hx
    rw [requiredSwitch_eq_of_source act B₀ E p g hfix
          hcompatP hsourceP htargetP x hx c hxc,
        requiredSwitch_eq_of_source act B₀ E q g hfix
          hcompatQ hsourceQ htargetQ x hxq c hxc]
    exact bitDiscrepancy_eq_of_equivalent
      act B₀ E p q g hfix hcompatP hcompatQ hpq
        x hx hxq c hxc
  · have hq : ¬ Nonempty (SourceWitness act B₀ E q c) := by
      rintro ⟨⟨x,hxq,hxc⟩⟩
      have hxp : x ∈ p.source := by
        rw [hsrc]
        exact hxq
      exact h ⟨⟨x, hxp, hxc⟩⟩
    rw [requiredSwitch_eq_false_of_no_source
          act B₀ E p g hfix hcompatP c h,
        requiredSwitch_eq_false_of_no_source
          act B₀ E q g hfix hcompatQ c hq]

end Sparsening
end AllThoseEPPA
