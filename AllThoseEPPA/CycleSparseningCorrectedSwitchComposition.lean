import AllThoseEPPA.CycleSparseningRequiredSwitchComp

/-!
# Conjugating and combining the canonical Boolean corrections

The cyclic correction attached to q is indexed by the source of q, whereas
the composite q ∘ p uses the source of p. Transporting by the composite
base automorphism converts this pullback to the correction transported only
by the second base automorphism.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Transporting a switch pulled back along gp through gq∘gp gives the
ordinary transport of that switch through gq. -/
theorem transportedSwitch_pullback
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s : Structure.BadCycleSequence B₀ E → Bool) :
    transportedSwitch act B₀ E (gq.comp gp) hfix
      (fun c => s (c.transport gp hfix)) =
      transportedSwitch act B₀ E gq hfix s := by
  funext c
  rcases (Structure.BadCycleSequence.transportEquiv
    (gq.comp gp) hfix).surjective c with ⟨d, rfl⟩
  have hseq : (d.transport gp hfix).transport gq hfix =
      d.transport (gq.comp gp) hfix :=
    Structure.BadCycleSequence.transport_comp d gq gp hfix
  calc
    transportedSwitch act B₀ E (gq.comp gp) hfix
        (fun t => s (t.transport gp hfix))
        (d.transport (gq.comp gp) hfix) =
      s (d.transport gp hfix) :=
      transportedSwitch_transport act B₀ E (gq.comp gp) hfix
        (fun t => s (t.transport gp hfix)) d
    _ = transportedSwitch act B₀ E gq hfix s
          (d.transport (gq.comp gp) hfix) := by
      rw [← hseq]
      exact
        (transportedSwitch_transport act B₀ E gq hfix s
          (d.transport gp hfix)).symm

/-- The canonical correction of a composite, after reindexing to its
target, is precisely the XOR of the corrections of the two lifts in the
coordinates of their common final target. -/
theorem transportedRequiredSwitch_comp
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
    transportedSwitch act B₀ E (gq.comp gp) hfix
      (requiredSwitch act B₀ E (q.comp p ht)
        (gq.comp gp) hfix hcomp) =
    switchSum B₀ E
      (transportedSwitch act B₀ E (gq.comp gp) hfix
        (requiredSwitch act B₀ E p gp hfix hcp))
      (transportedSwitch act B₀ E gq hfix
        (requiredSwitch act B₀ E q gq hfix hcq)) := by
  rw [requiredSwitch_comp act B₀ E p q gp gq hfix ht hcp hcq
    hcomp hsp htp hsq htq hsrc htgt]
  rw [transportedSwitch_sum act B₀ E (gq.comp gp) hfix]
  rw [transportedSwitch_pullback act B₀ E gp gq hfix
    (requiredSwitch act B₀ E q gq hfix hcq)]

end Sparsening
end AllThoseEPPA
