import AllThoseEPPA.FaithfulValuationGeneric

/-!
# Transport of faithful valuation structures
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type v}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α) (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)

/-- Fibre equivalence for valuation assignments over transported one-point
closures. -/
noncomputable def valuationAssignmentFibreEquiv [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (x : β)
    (z : B₀.closureAtSet (g x)) :
    ValuationFunction act A B₀ ψ
        (((closureTransportEquiv act B₀ g x).symm z).1) ≃
      ValuationFunction act A B₀ ψ z.1 := by
  let y := (closureTransportEquiv act B₀ g x).symm z
  have hbase : g y.1 = z.1 := by
    exact congrArg Subtype.val
      ((closureTransportEquiv act B₀ g x).apply_symm_apply z)
  exact
    (valuationFunctionEquiv act A B₀ ψ
      p g hsource htarget hcompat y.1).trans
      (Equiv.cast
        (congrArg
          (fun b : β => ValuationFunction act A B₀ ψ b)
          hbase))

/-- Transport an entire valuation assignment over a one-point closure. -/
noncomputable def valuationAssignmentEquiv [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (x : β) :
    ValuationAssignment act A B₀ ψ x ≃
      ValuationAssignment act A B₀ ψ (g x) :=
  Equiv.piCongr
    (W := fun y : B₀.closureAtSet x =>
      ValuationFunction act A B₀ ψ y.1)
    (Z := fun z : B₀.closureAtSet (g x) =>
      ValuationFunction act A B₀ ψ z.1)
    (closureTransportEquiv act B₀ g x)
    (fun y =>
      valuationFunctionEquiv act A B₀ ψ
        p g hsource htarget hcompat y.1)

/-- Evaluation of a transported valuation assignment at the transported
closure point. -/
theorem valuationAssignmentEquiv_apply_transport [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (x : β)
    (V : ValuationAssignment act A B₀ ψ x)
    (y : B₀.closureAtSet x) :
    valuationAssignmentEquiv act A B₀ ψ
        p g hsource htarget hcompat x V
        (closureTransportEquiv act B₀ g x y) =
      valuationFunctionEquiv act A B₀ ψ
        p g hsource htarget hcompat y.1 (V y) := by
  exact
    Equiv.piCongr_apply_apply
      (W := fun z : B₀.closureAtSet x =>
        ValuationFunction act A B₀ ψ z.1)
      (Z := fun z : B₀.closureAtSet (g x) =>
        ValuationFunction act A B₀ ψ z.1)
      (closureTransportEquiv act B₀ g x)
      (fun z =>
        valuationFunctionEquiv act A B₀ ψ
          p g hsource htarget hcompat z.1)
      V y

/-- Internal valuation points commute with assignment transport. -/
theorem valuationPointAt_assignment_transport [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (x : β)
    (V : ValuationAssignment act A B₀ ψ x)
    (y : B₀.closureAtSet x) :
    valuationPointAt act A B₀ ψ
        (valuationAssignmentEquiv act A B₀ ψ
          p g hsource htarget hcompat x V)
        (closureTransportEquiv act B₀ g x y) =
      transportValuationPoint act A B₀ ψ
        p g hsource htarget hcompat
        (valuationPointAt act A B₀ ψ V y) := by
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  exact heq_of_eq
    (valuationAssignmentEquiv_apply_transport
      act A B₀ ψ p g hsource htarget hcompat x V y)

/-- Transport of a generic valuation structure along a compatible base
automorphism. -/
noncomputable def ValuationStructure.transport [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    {x : β}
    (V : ValuationStructure act A B₀ ψ x) :
    ValuationStructure act A B₀ ψ (g x) := by
  let e := closureTransportEquiv act B₀ g x
  refine
    ⟨valuationAssignmentEquiv act A B₀ ψ
        p g hsource htarget hcompat x V.1, ?_⟩
  intro y z
  let y0 := e.symm y
  let z0 := e.symm z
  have hy : e y0 = y := e.apply_symm_apply y
  have hz : e z0 = z := e.apply_symm_apply z
  rw [← hy, ← hz]
  rw [
    valuationPointAt_assignment_transport
      act A B₀ ψ p g hsource htarget hcompat x V.1 y0,
    valuationPointAt_assignment_transport
      act A B₀ ψ p g hsource htarget hcompat x V.1 z0]
  exact
    areGeneric_transport act A B₀ ψ
      p g hsource htarget hcompat
      (V.2 y0 z0)

/-- Transport on faithful valuation structures is injective. -/
theorem ValuationStructure.transport_injective [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    {x : β} :
    Function.Injective
      (ValuationStructure.transport act A B₀ ψ
        p g hsource htarget hcompat :
          ValuationStructure act A B₀ ψ x →
            ValuationStructure act A B₀ ψ (g x)) := by
  intro V W hVW
  apply Subtype.ext
  apply
    (valuationAssignmentEquiv act A B₀ ψ
      p g hsource htarget hcompat x).injective
  exact congrArg Subtype.val hVW


/-- Transport commutes with restricting a valuation structure to a nested
one-point closure. -/
theorem ValuationStructure.transport_restrict [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    {x y : β}
    (V : ValuationStructure act A B₀ ψ x)
    (hy : y ∈ B₀.closureAtSet x) :
    ValuationStructure.transport act A B₀ ψ
        p g hsource htarget hcompat
        (V.restrict act A B₀ ψ y hy) =
      (ValuationStructure.transport act A B₀ ψ
        p g hsource htarget hcompat V).restrict
          act A B₀ ψ (g y)
          (automorphism_maps_closureAtSet act B₀ g hy) := by
  apply Subtype.ext
  funext z
  let eY := closureTransportEquiv act B₀ g y
  let z0 := eY.symm z
  have hz : eY z0 = z := eY.apply_symm_apply z
  rw [← hz]
  change
    valuationAssignmentEquiv act A B₀ ψ
        p g hsource htarget hcompat y
        (V.restrict act A B₀ ψ y hy).1
        (eY z0) =
      valuationAssignmentEquiv act A B₀ ψ
        p g hsource htarget hcompat x V.1
        (closureInclusion B₀
          (automorphism_maps_closureAtSet act B₀ g hy)
          (eY z0))
  rw [valuationAssignmentEquiv_apply_transport
    act A B₀ ψ p g hsource htarget hcompat
    y (V.restrict act A B₀ ψ y hy).1 z0]
  let W :=
    valuationAssignmentEquiv act A B₀ ψ
      p g hsource htarget hcompat x V.1
  let t₂ :=
    closureTransportEquiv act B₀ g x
      (closureInclusion B₀ hy z0)
  let t₁ :=
    closureInclusion B₀
      (automorphism_maps_closureAtSet act B₀ g hy)
      (eY z0)
  have ht : t₂ = t₁ := by
    exact
      closureTransportEquiv_closureInclusion
        act B₀ g hy z0
  have hdep : HEq (W t₂) (W t₁) := by
    have hp :
        (⟨t₂, W t₂⟩ :
          Σ t : B₀.closureAtSet (g x),
            ValuationFunction act A B₀ ψ t.1) =
        ⟨t₁, W t₁⟩ :=
      congrArg
        (fun t =>
          (⟨t, W t⟩ :
            Σ s : B₀.closureAtSet (g x),
              ValuationFunction act A B₀ ψ s.1))
        ht
    exact (Sigma.mk.inj_iff.mp hp).2
  have hr :=
    valuationAssignmentEquiv_apply_transport
      act A B₀ ψ p g hsource htarget hcompat
      x V.1 (closureInclusion B₀ hy z0)
  have hleft :
      HEq
        (valuationFunctionEquiv act A B₀ ψ
          p g hsource htarget hcompat z0.1
          ((V.restrict act A B₀ ψ y hy).1 z0))
        (W t₂) := by
    exact heq_of_eq hr.symm
  exact eq_of_heq (hleft.trans hdep)

end Faithful
end AllThoseEPPA
