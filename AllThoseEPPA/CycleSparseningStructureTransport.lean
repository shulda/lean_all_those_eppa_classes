import AllThoseEPPA.CycleSparseningTransportGeneric
import AllThoseEPPA.FaithfulClosureTransport

/-!
# Transport of cycle valuation structures through one-point closures

The closure transport is reused directly from the irreducible-faithful
construction. The only new ingredient is the cycle-valued genericity theorem.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Transport all valuation functions in a one-point closure by reindexing
the closure and the induced bad-cycle index sets simultaneously. -/
noncomputable def valuationAssignmentEquiv
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (x : V) :
    ValuationAssignment B₀ E x ≃ ValuationAssignment B₀ E (g x) :=
  Equiv.piCongr
    (W := fun y : B₀.closureAtSet x =>
      ValuationFunction B₀ E y.1)
    (Z := fun z : B₀.closureAtSet (g x) =>
      ValuationFunction B₀ E z.1)
    (Faithful.closureTransportEquiv act B₀ g x)
    (fun y =>
      valuationFunctionTransportEquiv act B₀ E g hfix y.1)

/-- Evaluating the transported assignment at a transported closure point. -/
theorem valuationAssignmentEquiv_apply_transport
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E) (x : V)
    (W : ValuationAssignment B₀ E x)
    (y : B₀.closureAtSet x) :
    valuationAssignmentEquiv act B₀ E g hfix x W
        (Faithful.closureTransportEquiv act B₀ g x y) =
      valuationFunctionTransportEquiv act B₀ E g hfix y.1 (W y) := by
  exact Equiv.piCongr_apply_apply
    (W := fun z : B₀.closureAtSet x => ValuationFunction B₀ E z.1)
    (Z := fun z : B₀.closureAtSet (g x) => ValuationFunction B₀ E z.1)
    (Faithful.closureTransportEquiv act B₀ g x)
    (fun z => valuationFunctionTransportEquiv act B₀ E g hfix z.1)
    W y

/-- Valuation points within a closure commute with assignment transport. -/
theorem valuationPointAt_assignment_transport
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E) (x : V)
    (W : ValuationAssignment B₀ E x)
    (y : B₀.closureAtSet x) :
    valuationPointAt B₀ E
        (valuationAssignmentEquiv act B₀ E g hfix x W)
        (Faithful.closureTransportEquiv act B₀ g x y) =
      valuationPointTransport act B₀ E g hfix
        (valuationPointAt B₀ E W y) := by
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  exact heq_of_eq
    (valuationAssignmentEquiv_apply_transport act B₀ E g hfix x W y)

/-- Generic valuation structures transport to generic valuation structures. -/
noncomputable def ValuationStructure.transport
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    {x : V} (W : ValuationStructure B₀ E x) :
    ValuationStructure B₀ E (g x) := by
  let e := Faithful.closureTransportEquiv act B₀ g x
  refine ⟨valuationAssignmentEquiv act B₀ E g hfix x W.1, ?_⟩
  intro y z
  let y0 := e.symm y
  let z0 := e.symm z
  have hy : e y0 = y := e.apply_symm_apply y
  have hz : e z0 = z := e.apply_symm_apply z
  rw [← hy, ← hz]
  rw [valuationPointAt_assignment_transport act B₀ E g hfix x W.1 y0,
      valuationPointAt_assignment_transport act B₀ E g hfix x W.1 z0]
  exact areGeneric_transport act B₀ E g hfix (W.2 y0 z0)

/-- Injectivity is inherited from the dependent product equivalence. -/
theorem ValuationStructure.transport_injective
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    {x : V} :
    Function.Injective
      (ValuationStructure.transport act B₀ E g hfix :
        ValuationStructure B₀ E x → ValuationStructure B₀ E (g x)) := by
  intro W Z hWZ
  apply Subtype.ext
  apply (valuationAssignmentEquiv act B₀ E g hfix x).injective
  exact congrArg Subtype.val hWZ

end Sparsening
end AllThoseEPPA
