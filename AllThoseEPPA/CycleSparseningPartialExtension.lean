import AllThoseEPPA.CycleSparseningPartialValuations

/-!
# The corrected lift extends a prescribed partial automorphism

This proof mirrors the successful `FaithfulExtension` formalization.  First
the valuation functions are corrected throughout one-point closures, then
the dependent witness vertices are identified via equality of their bases
and generic valuation structures.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Equality of witness vertices gives equality of their valuation functions
on a shared base coordinate, independently of membership proofs. -/
theorem witnessValuationAt_congr
    {u v : WitnessVertex B₀ E}
    (huv : u = v)
    (z : V)
    (hu : z ∈ B₀.closureAtSet (u.base B₀ E))
    (hv : z ∈ B₀.closureAtSet (v.base B₀ E)) :
    (u.valuation B₀ E).1 ⟨z, hu⟩ =
      (v.valuation B₀ E).1 ⟨z, hv⟩ := by
  subst v
  rfl

/-- The base lift followed by the uniquely required global correction
agrees literally with the given partial automorphism on its source. -/
theorem correctedWitnessVertex_eq_of_mem_source [Finite V]
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (hsource : WitnessSetGeneric B₀ E p.source)
    (htarget : WitnessSetGeneric B₀ E p.target)
    (w : WitnessVertex B₀ E) (hw : w ∈ p.source) :
    (w.transport act B₀ E g hfix).flip B₀ E
      (transportedSwitch act B₀ E g hfix
        (requiredSwitch act B₀ E p g hfix hcompat)) = p w := by
  generalize hpw : p w = pw
  rcases pw with ⟨b, Wp⟩
  have hbase : g (w.base B₀ E) = b := by
    have h := hcompat.2 w hw
    rw [hpw] at h
    exact h
  rw [Sigma.ext_iff]
  refine ⟨hbase, ?_⟩
  cases hbase
  change HEq
    ((ValuationStructure.transport act B₀ E g hfix
      (w.valuation B₀ E)).flip B₀ E
        (transportedSwitch act B₀ E g hfix
          (requiredSwitch act B₀ E p g hfix hcompat)))
    Wp
  rw [heq_iff_eq]
  apply Subtype.ext
  funext z
  let e := Faithful.closureTransportEquiv act B₀ g (w.base B₀ E)
  let y := e.symm z
  have hz : e y = z := e.apply_symm_apply z
  rw [← hz]
  change
    valuationFunctionFlip B₀ E
      (transportedSwitch act B₀ E g hfix
        (requiredSwitch act B₀ E p g hfix hcompat))
      (valuationAssignmentEquiv act B₀ E g hfix (w.base B₀ E)
        (w.valuation B₀ E).1 (e y)) =
      Wp.1 (e y)
  rw [valuationAssignmentEquiv_apply_transport act B₀ E g hfix
    (w.base B₀ E) (w.valuation B₀ E).1 y]
  let hy' :
      g y.1 ∈ B₀.closureAtSet ((p w).base B₀ E) := by
    have h := Faithful.automorphism_maps_closureAtSet act B₀ g y.2
    simpa [hcompat.2 w hw] using h
  have ht :
      valuationFunctionFlip B₀ E
        (transportedSwitch act B₀ E g hfix
          (requiredSwitch act B₀ E p g hfix hcompat))
        (valuationFunctionTransportEquiv act B₀ E g hfix y.1
          ((w.valuation B₀ E).1
            (⟨y.1, y.2⟩ : B₀.closureAtSet (w.base B₀ E)))) =
      ((p w).valuation B₀ E).1
        (⟨g y.1, hy'⟩ :
          B₀.closureAtSet ((p w).base B₀ E)) := by
    simpa [hy'] using
      (correctedValuationFunction_eq_of_mem_source
        act B₀ E p g hfix hcompat hsource htarget
        w hw y.1 y.2)
  have hgy :
      g y.1 ∈ B₀.closureAtSet (g (w.base B₀ E)) :=
    Faithful.automorphism_maps_closureAtSet act B₀ g y.2
  have hval :=
    witnessValuationAt_congr B₀ E hpw (g y.1) hy' hgy
  -- Normalize the target fibre to the explicit base coordinate `g y`
  -- before rewriting the equality of dependent valuation functions.
  change
    valuationFunctionFlip B₀ E
      (transportedSwitch act B₀ E g hfix
        (requiredSwitch act B₀ E p g hfix hcompat))
      (valuationFunctionTransportEquiv act B₀ E g hfix y.1
        ((w.valuation B₀ E).1 y)) =
      Wp.1
        (⟨g y.1, hgy⟩ :
          B₀.closureAtSet (g (w.base B₀ E)))
  rw [ht]
  simpa [WitnessVertex.valuation, WitnessVertex.base] using hval

/-- The corrected lift is an actual extension along the identity embedding. -/
theorem correctedLift_extends [Finite V]
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (hsource : WitnessSetGeneric B₀ E p.source)
    (htarget : WitnessSetGeneric B₀ E p.target) :
    Structure.ExtendsAlong act
      (Structure.Embedding.id (witnessStructure B₀ E))
      p
      ((witnessFlipAutomorphism B₀ E
        (transportedSwitch act B₀ E g hfix
          (requiredSwitch act B₀ E p g hfix hcompat)) act).comp
        (baseAutomorphismLift act B₀ E g hfix)) := by
  constructor
  · change ((1 : Γ) * g.lang) * (1 : Γ) = (1 : Γ) * p.lang
    simpa [hcompat.1]
  · intro w hw
    change
      (w.transport act B₀ E g hfix).flip B₀ E
        (transportedSwitch act B₀ E g hfix
          (requiredSwitch act B₀ E p g hfix hcompat)) = p w
    exact correctedWitnessVertex_eq_of_mem_source
      act B₀ E p g hfix hcompat hsource htarget w hw

/-- The extension part of the induced-cycle sparsening lemma: a generic
partial automorphism whose base projection extends to an E-preserving
automorphism of B₀ extends to the full cycle-sparsening witness. -/
theorem sparseningExtension [Finite V]
    (p : Structure.PartialAutomorphism act (witnessStructure B₀ E))
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (hcompat : BaseCompatible act B₀ E p g)
    (hsource : WitnessSetGeneric B₀ E p.source)
    (htarget : WitnessSetGeneric B₀ E p.target) :
    ∃ h : Structure.Automorphism act (witnessStructure B₀ E),
      Structure.ExtendsAlong act
        (Structure.Embedding.id (witnessStructure B₀ E))
        p h := by
  refine ⟨(witnessFlipAutomorphism B₀ E
      (transportedSwitch act B₀ E g hfix
        (requiredSwitch act B₀ E p g hfix hcompat)) act).comp
      (baseAutomorphismLift act B₀ E g hfix), ?_⟩
  exact correctedLift_extends
    act B₀ E p g hfix hcompat hsource htarget

end Sparsening
end AllThoseEPPA
