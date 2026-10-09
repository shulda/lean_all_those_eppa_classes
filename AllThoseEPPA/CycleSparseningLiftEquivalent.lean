import AllThoseEPPA.CycleSparseningCanonicalLift
import AllThoseEPPA.CycleSparseningSwitchEquivalent

/-!
# Invariance of the total sparsening lift under equivalent partial maps

The canonical Boolean correction is independent of the concrete
representation of its partial automorphism. As the base automorphism is
fixed, its corrected total lift is independent as well.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Equivalent generic partial maps, with a common compatible base
automorphism, receive the same total sparsening extension. -/
theorem sparseningLiftAutomorphism_eq_of_equivalent [Finite V]
    (p q : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcp : BaseCompatible act B₀ E p g)
    (hcq : BaseCompatible act B₀ E q g)
    (hsp : WitnessSetGeneric B₀ E p.source)
    (htp : WitnessSetGeneric B₀ E p.target)
    (hsq : WitnessSetGeneric B₀ E q.source)
    (htq : WitnessSetGeneric B₀ E q.target)
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    sparseningLiftAutomorphism act B₀ E p g hfix hcp =
      sparseningLiftAutomorphism act B₀ E q g hfix hcq := by
  have hs := requiredSwitch_eq_of_equivalent
    act B₀ E p q g hfix hcp hcq hsp htp hsq htq hpq
  change
    (witnessFlipAutomorphism B₀ E
       (transportedSwitch act B₀ E g hfix
          (requiredSwitch act B₀ E p g hfix hcp)) act).comp
        (baseAutomorphismLift act B₀ E g hfix) =
    (witnessFlipAutomorphism B₀ E
       (transportedSwitch act B₀ E g hfix
          (requiredSwitch act B₀ E q g hfix hcq)) act).comp
        (baseAutomorphismLift act B₀ E g hfix)
  rw [hs]

end Sparsening
end AllThoseEPPA
