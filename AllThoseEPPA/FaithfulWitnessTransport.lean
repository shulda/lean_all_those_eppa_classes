import AllThoseEPPA.FaithfulValuationStructureTransport

/-!
# Transport of faithful witness vertices
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

/-- Transport a faithful witness vertex along a compatible base
automorphism. -/
noncomputable def WitnessVertex.transport [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ) :
    WitnessVertex act A B₀ ψ :=
  Sigma.map g
    (fun _ =>
      ValuationStructure.transport act A B₀ ψ
        p g hsource htarget hcompat) w

@[simp] theorem WitnessVertex.transport_base [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ) :
    (WitnessVertex.transport act A B₀ ψ
      p g hsource htarget hcompat w).base =
      g w.base :=
  rfl

/-- Internal valuation points of witness vertices commute with transport. -/
theorem WitnessVertex.transport_pointAt [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ)
    (y : B₀.closureAtSet w.base) :
    (WitnessVertex.transport act A B₀ ψ
        p g hsource htarget hcompat w).pointAt
        act A B₀ ψ
        (closureTransportEquiv act B₀ g w.base y) =
      transportValuationPoint act A B₀ ψ
        p g hsource htarget hcompat
        (w.pointAt act A B₀ ψ y) := by
  apply Sigma.ext rfl
  exact heq_of_eq
    (valuationAssignmentEquiv_apply_transport
      act A B₀ ψ p g hsource htarget hcompat
      w.base w.valuation.1 y)

/-- Transport of faithful witness vertices is injective. -/
theorem WitnessVertex.transport_injective [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    Function.Injective
      (WitnessVertex.transport act A B₀ ψ
        p g hsource htarget hcompat) := by
  exact
    g.toEquiv.injective.sigma_map
      (fun x =>
        ValuationStructure.transport_injective
          act A B₀ ψ p g hsource htarget hcompat)

/-- Since the faithful witness is finite, injective transport is a
permutation. -/
noncomputable def witnessEquiv [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g) :
    WitnessVertex act A B₀ ψ ≃
      WitnessVertex act A B₀ ψ := by
  let f :=
    WitnessVertex.transport act A B₀ ψ
      p g hsource htarget hcompat
  have hf : Function.Injective f :=
    WitnessVertex.transport_injective
      act A B₀ ψ p g hsource htarget hcompat
  letI : Finite (WitnessVertex act A B₀ ψ) :=
    witnessVertex_finite act A B₀ ψ
  have hs : Function.Surjective f :=
    Finite.injective_iff_surjective.mp hf
  exact Equiv.ofBijective f ⟨hf, hs⟩

@[simp] theorem witnessEquiv_apply [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ) :
    witnessEquiv act A B₀ ψ
        p g hsource htarget hcompat w =
      WitnessVertex.transport act A B₀ ψ
        p g hsource htarget hcompat w :=
  rfl

/-- Genericity of witness families is preserved and reflected by witness
transport. -/
theorem witnessFamilyGeneric_transport_iff [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    {ι : Type*}
    (ws : ι → WitnessVertex act A B₀ ψ) :
    WitnessFamilyGeneric act A B₀ ψ
      (fun i =>
        WitnessVertex.transport act A B₀ ψ
          p g hsource htarget hcompat (ws i)) ↔
    WitnessFamilyGeneric act A B₀ ψ ws := by
  constructor
  · intro hgen i j y z
    have ht :=
      hgen i j
        (closureTransportEquiv act B₀ g (ws i).base y)
        (closureTransportEquiv act B₀ g (ws j).base z)
    rw [
      WitnessVertex.transport_pointAt
        act A B₀ ψ p g hsource htarget hcompat (ws i) y,
      WitnessVertex.transport_pointAt
        act A B₀ ψ p g hsource htarget hcompat (ws j) z] at ht
    exact
      areGeneric_of_transport act A B₀ ψ
        p g hsource htarget hcompat ht
  · intro hgen i j y z
    let ei := closureTransportEquiv act B₀ g (ws i).base
    let ej := closureTransportEquiv act B₀ g (ws j).base
    let y0 := ei.symm y
    let z0 := ej.symm z
    have hy : ei y0 = y := ei.apply_symm_apply y
    have hz : ej z0 = z := ej.apply_symm_apply z
    rw [← hy, ← hz]
    rw [
      WitnessVertex.transport_pointAt
        act A B₀ ψ p g hsource htarget hcompat (ws i) y0,
      WitnessVertex.transport_pointAt
        act A B₀ ψ p g hsource htarget hcompat (ws j) z0]
    exact
      areGeneric_transport act A B₀ ψ
        p g hsource htarget hcompat
        (hgen i j y0 z0)

/-- The faithful witness permutation transports relations exactly. -/
theorem witnessRelation_transport_iff [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    {n : ℕ} (R : L.RelSymbol n)
    (ws : Fin n → WitnessVertex act A B₀ ψ) :
    (witnessStructure act A B₀ ψ).rel
        (act.onRel g.lang R)
        (witnessEquiv act A B₀ ψ
          p g hsource htarget hcompat ∘ ws) ↔
      (witnessStructure act A B₀ ψ).rel R ws := by
  change
    (B₀.rel (act.onRel g.lang R)
        (fun i => g (ws i).base) ∧
      WitnessFamilyGeneric act A B₀ ψ
        (fun i =>
          WitnessVertex.transport act A B₀ ψ
            p g hsource htarget hcompat (ws i))) ↔
    (B₀.rel R (fun i => (ws i).base) ∧
      WitnessFamilyGeneric act A B₀ ψ ws)
  exact and_congr
    (Structure.Automorphism.map_rel_iff
      act g R (fun i => (ws i).base))
    (witnessFamilyGeneric_transport_iff
      act A B₀ ψ p g hsource htarget hcompat ws)

end Faithful
end AllThoseEPPA
