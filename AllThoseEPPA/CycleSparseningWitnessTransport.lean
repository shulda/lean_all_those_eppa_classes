import AllThoseEPPA.CycleSparseningStructureTransport
import AllThoseEPPA.CycleSparseningTransportGenericReflect

/-!
# Transporting the entire cycle-sparsening witness

The construction is the same dependent-Sigma transport as in
`FaithfulWitnessTransport`, with the index automorphism and its ordinary
Boolean fibre equivalences replacing faithful label completions.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Apply a base automorphism to the centre and transport its whole
generic valuation structure. -/
noncomputable def WitnessVertex.transport
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (w : WitnessVertex B₀ E) : WitnessVertex B₀ E :=
  Sigma.map g
    (fun _ => ValuationStructure.transport act B₀ E g hfix) w

@[simp] theorem WitnessVertex.transport_base
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (w : WitnessVertex B₀ E) :
    (w.transport act B₀ E g hfix).base B₀ E = g (w.base B₀ E) :=
  rfl

/-- The valuation at a point in a one-point closure commutes with transport. -/
theorem WitnessVertex.transport_pointAt
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (w : WitnessVertex B₀ E)
    (y : B₀.closureAtSet (w.base B₀ E)) :
    (w.transport act B₀ E g hfix).pointAt B₀ E
        (Faithful.closureTransportEquiv act B₀ g (w.base B₀ E) y) =
      valuationPointTransport act B₀ E g hfix
        (w.pointAt B₀ E y) := by
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  exact heq_of_eq
    (valuationAssignmentEquiv_apply_transport act B₀ E g hfix
      (w.base B₀ E) (w.valuation B₀ E).1 y)

/-- The transported witness vertex is injective. -/
theorem WitnessVertex.transport_injective
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E) :
    Function.Injective
      (WitnessVertex.transport act B₀ E g hfix) := by
  exact
    g.toEquiv.injective.sigma_map
      (fun x => ValuationStructure.transport_injective
        act B₀ E g hfix (x := x))

/-- On a finite witness, injective transport is a permutation. -/
noncomputable def witnessEquiv [Finite V]
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E) :
    WitnessVertex B₀ E ≃ WitnessVertex B₀ E := by
  let f := WitnessVertex.transport act B₀ E g hfix
  have hf : Function.Injective f :=
    WitnessVertex.transport_injective act B₀ E g hfix
  letI : Finite (WitnessVertex B₀ E) :=
    witnessVertex_finite B₀ E
  have hs : Function.Surjective f :=
    Finite.injective_iff_surjective.mp hf
  exact Equiv.ofBijective f ⟨hf, hs⟩

@[simp] theorem witnessEquiv_apply [Finite V]
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (w : WitnessVertex B₀ E) :
    witnessEquiv act B₀ E g hfix w =
      w.transport act B₀ E g hfix :=
  rfl

/-- Transport preserves and reflects genericity of families of
witness vertices and all the valuation points in their closures. -/
theorem witnessFamilyGeneric_transport_iff
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    {ι : Type*} (ws : ι → WitnessVertex B₀ E) :
    WitnessFamilyGeneric B₀ E
      (fun i => (ws i).transport act B₀ E g hfix) ↔
    WitnessFamilyGeneric B₀ E ws := by
  constructor
  · intro hgen i j y z
    have ht :=
      hgen i j
        (Faithful.closureTransportEquiv act B₀ g
          ((ws i).base B₀ E) y)
        (Faithful.closureTransportEquiv act B₀ g
          ((ws j).base B₀ E) z)
    rw [
      WitnessVertex.transport_pointAt act B₀ E g hfix (ws i) y,
      WitnessVertex.transport_pointAt act B₀ E g hfix (ws j) z] at ht
    exact areGeneric_of_transport act B₀ E g hfix ht
  · intro hgen i j y z
    let ei := Faithful.closureTransportEquiv act B₀ g ((ws i).base B₀ E)
    let ej := Faithful.closureTransportEquiv act B₀ g ((ws j).base B₀ E)
    let y0 := ei.symm y
    let z0 := ej.symm z
    have hy : ei y0 = y := ei.apply_symm_apply y
    have hz : ej z0 = z := ej.apply_symm_apply z
    rw [← hy, ← hz]
    rw [
      WitnessVertex.transport_pointAt act B₀ E g hfix (ws i) y0,
      WitnessVertex.transport_pointAt act B₀ E g hfix (ws j) z0]
    exact areGeneric_transport act B₀ E g hfix (hgen i j y0 z0)

/-- The induced permutation transports every relational interpretation. -/
theorem witnessRelation_transport_iff [Finite V]
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    {n : ℕ} (R : L.RelSymbol n)
    (ws : Fin n → WitnessVertex B₀ E) :
    (witnessStructure B₀ E).rel (act.onRel g.lang R)
        (witnessEquiv act B₀ E g hfix ∘ ws) ↔
      (witnessStructure B₀ E).rel R ws := by
  change
    (B₀.rel (act.onRel g.lang R)
        (fun i => g ((ws i).base B₀ E)) ∧
      WitnessFamilyGeneric B₀ E
        (fun i => (ws i).transport act B₀ E g hfix)) ↔
    (B₀.rel R (fun i => (ws i).base B₀ E) ∧
      WitnessFamilyGeneric B₀ E ws)
  exact and_congr
    (Structure.Automorphism.map_rel_iff
      (g := g) R (fun i => (ws i).base B₀ E))
    (witnessFamilyGeneric_transport_iff act B₀ E g hfix ws)

end Sparsening
end AllThoseEPPA
