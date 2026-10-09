import AllThoseEPPA.CycleSparseningSwitchTransport
import AllThoseEPPA.CycleSparseningLiftAutomorphism

/-!
# Semidirect-product commutation of base and flip automorphisms

The lift of g conjugates the global switch indexed by s to the one
obtained by pulling s back under the induced permutation of bad cycles.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- The semidirect commutation relation on the entire witness carrier. -/
theorem WitnessVertex.transport_flip
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s : Structure.BadCycleSequence B₀ E → Bool)
    (w : WitnessVertex B₀ E) :
    (w.flip B₀ E s).transport act B₀ E g hfix =
      (w.transport act B₀ E g hfix).flip B₀ E
        (transportedSwitch act B₀ E g hfix s) := by
  rcases w with ⟨x, W⟩
  have hW :=
    ValuationStructure.transport_flip act B₀ E g hfix s W
  change
    (⟨g x, ValuationStructure.transport act B₀ E g hfix
        (W.flip B₀ E s)⟩ : WitnessVertex B₀ E) =
      ⟨g x, (ValuationStructure.transport act B₀ E g hfix W).flip
        B₀ E (transportedSwitch act B₀ E g hfix s)⟩
  exact congrArg
    (fun Q : ValuationStructure B₀ E (g x) =>
      (⟨g x, Q⟩ : WitnessVertex B₀ E)) hW

/-- The lift of a base automorphism and a global Boolean switch obey
the natural semidirect-product commutation law. -/
theorem baseAutomorphismLift_comp_flip [Finite V]
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (s : Structure.BadCycleSequence B₀ E → Bool) :
    (baseAutomorphismLift act B₀ E g hfix).comp
      (witnessFlipAutomorphism B₀ E s act) =
    (witnessFlipAutomorphism B₀ E
      (transportedSwitch act B₀ E g hfix s) act).comp
      (baseAutomorphismLift act B₀ E g hfix) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · simp
  · intro w
    change
      (w.flip B₀ E s).transport act B₀ E g hfix =
      (w.transport act B₀ E g hfix).flip B₀ E
        (transportedSwitch act B₀ E g hfix s)
    exact WitnessVertex.transport_flip act B₀ E g hfix s w

end Sparsening
end AllThoseEPPA
