import AllThoseEPPA.CycleSparseningWitnessTransport
import AllThoseEPPA.CycleSparseningTransportRestriction
import AllThoseEPPA.FaithfulWitnessFunctionTransport

/-!
# Preservation of unary functions under cycle-index transport

The proof is deliberately parallel to the already formalized faithful
witness function-transport lemma. All closure and base-fibre lemmas are reused.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ] {V : Type w}
variable (act : L.Action Γ) (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Transport of a function-value vertex is the function-value vertex
of the transported valuation structure. -/
theorem functionValueVertex_transport [Finite V]
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    (w : WitnessVertex B₀ E)
    {n : ℕ} (F : L.FuncSymbol n)
    (y : V)
    (hy : y ∈ B₀.func F (fun _ => (w.base B₀ E))) :
    witnessEquiv act B₀ E g hfix
        (functionValueVertex B₀ E w F y hy) =
      functionValueVertex B₀ E
        (w.transport act B₀ E g hfix)
        (act.onFunc g.lang F) (g y)
        (Faithful.baseFunction_mem_transport act B₀ g F hy) := by
  rw [witnessEquiv_apply]
  rw [Sigma.ext_iff]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  change
    ValuationStructure.transport act B₀ E g hfix
        ((w.valuation B₀ E).restrict B₀ E y
          (func_mem_closureAtSet B₀ F hy)) =
      (ValuationStructure.transport act B₀ E g hfix
          (w.valuation B₀ E)).restrict
        B₀ E (g y)
        (Faithful.automorphism_maps_closureAtSet act B₀ g
          (func_mem_closureAtSet B₀ F hy))
  exact ValuationStructure.transport_restrict
    act B₀ E g hfix (w.valuation B₀ E)
    (func_mem_closureAtSet B₀ F hy)

/-- A transported witness permutation maps every unary function-value set
onto precisely the corresponding function-value set. -/
theorem witnessFunction_transport [Finite V]
    (g : Structure.Automorphism act B₀)
    (hfix : act.FixesRel E)
    {n : ℕ} (F : L.FuncSymbol n)
    (ws : Fin n → WitnessVertex B₀ E) :
    Structure.imageSet (witnessEquiv act B₀ E g hfix)
      ((witnessStructure B₀ E).func F ws) =
    (witnessStructure B₀ E).func (act.onFunc g.lang F)
      (witnessEquiv act B₀ E g hfix ∘ ws) := by
  let w := ws (UnaryFunctions.unaryIndex F)
  have hws : ws = fun _ => w := by
    simpa [w] using (UnaryFunctions.unaryTuple_eq_constant F ws)
  rw [hws]
  change
    Structure.imageSet (witnessEquiv act B₀ E g hfix)
      ((witnessStructure B₀ E).func F (fun _ => w)) =
    (witnessStructure B₀ E).func (act.onFunc g.lang F)
      (fun _ => witnessEquiv act B₀ E g hfix w)
  ext z
  constructor
  · rintro ⟨z₀, hz₀, rfl⟩
    change
      ∃ (y : V)
        (hy : y ∈ B₀.func F (fun _ => w.base B₀ E)),
        z₀ = functionValueVertex B₀ E w F y hy at hz₀
    rcases hz₀ with ⟨y, hy, rfl⟩
    change
      ∃ (t : V)
        (ht : t ∈ B₀.func (act.onFunc g.lang F)
          (fun _ => g (w.base B₀ E))),
        witnessEquiv act B₀ E g hfix
            (functionValueVertex B₀ E w F y hy) =
          functionValueVertex B₀ E
            (w.transport act B₀ E g hfix)
            (act.onFunc g.lang F) t ht
    exact ⟨g y,
      Faithful.baseFunction_mem_transport act B₀ g F hy,
      functionValueVertex_transport act B₀ E g hfix w F y hy⟩
  · intro hz
    change
      ∃ (y : V)
        (hy : y ∈ B₀.func (act.onFunc g.lang F)
          (fun _ => g (w.base B₀ E))),
        z = functionValueVertex B₀ E
          (w.transport act B₀ E g hfix)
          (act.onFunc g.lang F) y hy at hz
    rcases hz with ⟨y, hy, rfl⟩
    let y₀ := g.symm y
    have hy₀ : y₀ ∈ B₀.func F (fun _ => w.base B₀ E) := by
      apply (Faithful.baseFunction_mem_transport_iff act B₀ g F).1
      simpa [y₀] using hy
    refine ⟨functionValueVertex B₀ E w F y₀ hy₀, ?_, ?_⟩
    · change
        ∃ (t : V)
          (ht : t ∈ B₀.func F (fun _ => w.base B₀ E)),
          functionValueVertex B₀ E w F y₀ hy₀ =
            functionValueVertex B₀ E w F t ht
      exact ⟨y₀, hy₀, rfl⟩
    · have ht :=
        functionValueVertex_transport act B₀ E g hfix
          w F y₀ hy₀
      simpa [y₀] using ht

end Sparsening
end AllThoseEPPA
