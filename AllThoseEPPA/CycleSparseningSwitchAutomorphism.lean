import AllThoseEPPA.CycleSparseningSwitchWitness

/-! Every global assignment of Boolean cycle switches acts by an
automorphism on the cycle-sparsening witness, independently of the base. -/

namespace AllThoseEPPA
namespace Sparsening

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}
variable (B₀ : Structure L V) (E : L.RelSymbol 2)
variable (switch : Structure.BadCycleSequence B₀ E → Bool)

/-- Switches commute with all unary function-value witness vertices. -/
theorem functionValueVertex_flip
    (w : WitnessVertex B₀ E)
    {n : ℕ} (F : L.FuncSymbol n)
    (y : V) (hy : y ∈ B₀.func F (fun _ => w.base B₀ E)) :
    (functionValueVertex B₀ E w F y hy).flip B₀ E switch =
      functionValueVertex B₀ E (w.flip B₀ E switch) F y hy := by
  apply Sigma.ext rfl
  apply heq_of_eq
  change
    ((w.2.restrict B₀ E y (func_mem_closureAtSet B₀ F hy)).flip
      B₀ E switch) =
    (w.2.flip B₀ E switch).restrict B₀ E y
      (func_mem_closureAtSet B₀ F hy)
  exact (ValuationStructure.flip_restrict B₀ E switch w.2
    (func_mem_closureAtSet B₀ F hy)).symm

/-- Switching is its own inverse, so no finiteness is needed for bijectivity. -/
def witnessFlipEquiv : WitnessVertex B₀ E ≃ WitnessVertex B₀ E where
  toFun := WitnessVertex.flip B₀ E switch
  invFun := WitnessVertex.flip B₀ E switch
  left_inv := WitnessVertex.flip_flip B₀ E switch
  right_inv := WitnessVertex.flip_flip B₀ E switch

@[simp] theorem witnessFlipEquiv_apply (w : WitnessVertex B₀ E) :
    witnessFlipEquiv B₀ E switch w = w.flip B₀ E switch :=
  rfl

end Sparsening
end AllThoseEPPA
