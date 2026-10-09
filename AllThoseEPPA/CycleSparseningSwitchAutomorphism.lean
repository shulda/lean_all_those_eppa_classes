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

/-- The pure Boolean switch preserves and reflects every relation tuple. -/
theorem witnessRelation_flip_iff
    {n : ℕ} (R : L.RelSymbol n)
    (ws : Fin n → WitnessVertex B₀ E) :
    (witnessStructure B₀ E).rel R
        (witnessFlipEquiv B₀ E switch ∘ ws) ↔
    (witnessStructure B₀ E).rel R ws := by
  change
    (B₀.rel R (fun i => (ws i).base B₀ E) ∧
      WitnessFamilyGeneric B₀ E
        (fun i => (ws i).flip B₀ E switch)) ↔
    (B₀.rel R (fun i => (ws i).base B₀ E) ∧
      WitnessFamilyGeneric B₀ E ws)
  exact and_congr Iff.rfl
    (witnessFamilyGeneric_flip_iff B₀ E switch ws)

/-- Global cycle switches preserve unary function values by equality. -/
theorem witnessFunction_flip
    {n : ℕ} (F : L.FuncSymbol n)
    (ws : Fin n → WitnessVertex B₀ E) :
    Structure.imageSet (witnessFlipEquiv B₀ E switch)
      ((witnessStructure B₀ E).func F ws) =
    (witnessStructure B₀ E).func F
      (witnessFlipEquiv B₀ E switch ∘ ws) := by
  let w := ws (UnaryFunctions.unaryIndex F)
  have hws : ws = fun _ => w := by
    simpa [w] using UnaryFunctions.unaryTuple_eq_constant F ws
  rw [hws]
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    change
      ∃ (y : V)
        (hy : y ∈ B₀.func F (fun _ => w.base B₀ E)),
        v = functionValueVertex B₀ E w F y hy at hv
    rcases hv with ⟨y, hy, rfl⟩
    change
      ∃ (t : V)
        (ht : t ∈ B₀.func F (fun _ => w.base B₀ E)),
        (functionValueVertex B₀ E w F y hy).flip
            B₀ E switch =
          functionValueVertex B₀ E
            (w.flip B₀ E switch) F t ht
    exact ⟨y, hy, functionValueVertex_flip B₀ E switch w F y hy⟩
  · intro hz
    change
      ∃ (y : V)
        (hy : y ∈ B₀.func F (fun _ => w.base B₀ E)),
        z =
          functionValueVertex B₀ E
            (w.flip B₀ E switch) F y hy at hz
    rcases hz with ⟨y, hy, rfl⟩
    refine ⟨functionValueVertex B₀ E w F y hy, ?_, ?_⟩
    · change
        ∃ (t : V)
          (ht : t ∈ B₀.func F (fun _ => w.base B₀ E)),
          functionValueVertex B₀ E w F y hy =
            functionValueVertex B₀ E w F t ht
      exact ⟨y, hy, rfl⟩
    · exact functionValueVertex_flip B₀ E switch w F y hy


/-- Every global assignment of 0/1 cycle switches gives an automorphism of
the sparsening witness fixing each base coordinate. -/
noncomputable def witnessFlipAutomorphism
    {Γ : Type*} [Group Γ] (act : L.Action Γ) :
    Structure.Automorphism act (witnessStructure B₀ E) where
  toPartialIsomorphism :=
    { lang := 1
      toPartialEquiv := (witnessFlipEquiv B₀ E switch).toPartialEquiv
      source_closed := (witnessStructure B₀ E).isClosed_univ
      target_closed := (witnessStructure B₀ E).isClosed_univ
      map_rel_iff := by
        intro n R ws hws
        simpa using witnessRelation_flip_iff B₀ E switch R ws
      map_func := by
        intro n F ws hws
        simpa using witnessFunction_flip B₀ E switch F ws }
  source_eq_univ := rfl
  target_eq_univ := rfl

@[simp] theorem witnessFlipAutomorphism_apply
    {Γ : Type*} [Group Γ] (act : L.Action Γ)
    (w : WitnessVertex B₀ E) :
    witnessFlipAutomorphism B₀ E switch act w =
      w.flip B₀ E switch :=
  rfl

@[simp] theorem witnessFlipAutomorphism_lang
    {Γ : Type*} [Group Γ] (act : L.Action Γ) :
    (witnessFlipAutomorphism B₀ E switch act).lang = 1 :=
  rfl


end Sparsening
end AllThoseEPPA
