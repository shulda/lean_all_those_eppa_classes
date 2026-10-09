import AllThoseEPPA.CycleSparseningBaseCoherence
import AllThoseEPPA.CycleSparseningCorrectedSwitchComposition

/-!
# Coherent composition of corrected sparsening automorphisms

The corrected lift of q ∘ p is the product of the corrected lifts of
q and p.  This is the semidirect product law: the flip attached to p is
transported by gq, then combined by XOR with the flip attached to q.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- The semidirect composition identity for arbitrary Boolean source
switches, regardless of whether they come from partial automorphisms. -/
theorem totalCorrectedLift_comp [Finite V]
    (gp gq : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (sp sq : Structure.BadCycleSequence B₀ E → Bool) :
    ((witnessFlipAutomorphism B₀ E
        (transportedSwitch act B₀ E (gq.comp gp) hfix
          (switchSum B₀ E sp
            (fun c => sq (c.transport gp hfix)))) act).comp
      (baseAutomorphismLift act B₀ E (gq.comp gp) hfix)) =
    ((witnessFlipAutomorphism B₀ E
        (transportedSwitch act B₀ E gq hfix sq) act).comp
      (baseAutomorphismLift act B₀ E gq hfix)).comp
    ((witnessFlipAutomorphism B₀ E
        (transportedSwitch act B₀ E gp hfix sp) act).comp
      (baseAutomorphismLift act B₀ E gp hfix)) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · simp
  · intro w
    let s₁ := transportedSwitch act B₀ E gp hfix sp
    let s₁q := transportedSwitch act B₀ E gq hfix s₁
    let s₂ := transportedSwitch act B₀ E gq hfix sq
    have hs :
        transportedSwitch act B₀ E (gq.comp gp) hfix
          (switchSum B₀ E sp (fun c => sq (c.transport gp hfix))) =
        switchSum B₀ E s₁q s₂ := by
      rw [transportedSwitch_sum act B₀ E (gq.comp gp) hfix]
      rw [transportedSwitch_comp act B₀ E gq gp hfix sp]
      exact congrArg (switchSum B₀ E s₁q)
        (transportedSwitch_pullback act B₀ E gp gq hfix sq)
    change
      (w.transport act B₀ E (gq.comp gp) hfix).flip B₀ E
        (transportedSwitch act B₀ E (gq.comp gp) hfix
          (switchSum B₀ E sp (fun c => sq (c.transport gp hfix)))) =
      (((w.transport act B₀ E gp hfix).flip B₀ E s₁).transport
        act B₀ E gq hfix).flip B₀ E s₂
    rw [hs]
    have hflip :
        ((w.transport act B₀ E (gq.comp gp) hfix).flip B₀ E s₁q).flip
            B₀ E s₂ =
          (w.transport act B₀ E (gq.comp gp) hfix).flip B₀ E
            (switchSum B₀ E s₁q s₂) := by
      rw [WitnessVertex.flip_comp B₀ E s₂ s₁q]
      rw [switchSum_comm B₀ E s₂ s₁q]
    rw [← hflip]
    rw [WitnessVertex.transport_flip act B₀ E gq hfix s₁
      (w.transport act B₀ E gp hfix)]
    rw [WitnessVertex.transport_comp act B₀ E gp gq hfix w]

/-- The canonical source-supported lift respects exactly the composition
law for compatible generic partial automorphisms. -/
theorem sparseningLiftAutomorphism_comp [Finite V]
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
    sparseningLiftAutomorphism act B₀ E (q.comp p ht)
        (gq.comp gp) hfix hcomp =
      (sparseningLiftAutomorphism act B₀ E q gq hfix hcq).comp
        (sparseningLiftAutomorphism act B₀ E p gp hfix hcp) := by
  have hswitch := requiredSwitch_comp act B₀ E p q gp gq hfix
    ht hcp hcq hcomp hsp htp hsq htq hsrc htgt
  change
    (witnessFlipAutomorphism B₀ E
      (transportedSwitch act B₀ E (gq.comp gp) hfix
        (requiredSwitch act B₀ E (q.comp p ht)
          (gq.comp gp) hfix hcomp)) act).comp
      (baseAutomorphismLift act B₀ E (gq.comp gp) hfix) =
    ((witnessFlipAutomorphism B₀ E
      (transportedSwitch act B₀ E gq hfix
        (requiredSwitch act B₀ E q gq hfix hcq)) act).comp
      (baseAutomorphismLift act B₀ E gq hfix)).comp
    ((witnessFlipAutomorphism B₀ E
      (transportedSwitch act B₀ E gp hfix
        (requiredSwitch act B₀ E p gp hfix hcp)) act).comp
      (baseAutomorphismLift act B₀ E gp hfix))
  rw [hswitch]
  exact totalCorrectedLift_comp act B₀ E gp gq hfix
    (requiredSwitch act B₀ E p gp hfix hcp)
    (requiredSwitch act B₀ E q gq hfix hcq)

end Sparsening
end AllThoseEPPA
