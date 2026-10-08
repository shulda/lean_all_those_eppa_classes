import AllThoseEPPA.FaithfulWitnessTransport

/-!
# Unary-function transport for the faithful witness
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

/-- Membership in a base-witness unary function fibre is transported exactly
by a total base automorphism. -/
theorem baseFunction_mem_transport_iff
    (g : Structure.Automorphism act B₀)
    {x y : β} {n : ℕ} (F : L.FuncSymbol n) :
    g y ∈
        B₀.func (act.onFunc g.lang F) (fun _ => g x) ↔
      y ∈ B₀.func F (fun _ => x) := by
  have hmap :=
    Structure.Automorphism.map_func
      act g F (fun _ => x)
  constructor
  · intro hy
    have hyImg :
        g y ∈
          Structure.imageSet g (B₀.func F (fun _ => x)) := by
      rw [hmap]
      simpa [Function.comp_def] using hy
    rcases hyImg with ⟨z, hz, hzy⟩
    have hzy' : z = y :=
      g.toEquiv.injective hzy
    simpa [hzy'] using hz
  · intro hy
    have hyImg :
        g y ∈
          Structure.imageSet g (B₀.func F (fun _ => x)) :=
      ⟨y, hy, rfl⟩
    rw [hmap] at hyImg
    simpa [Function.comp_def] using hyImg

/-- A convenient one-way form of base function transport. -/
theorem baseFunction_mem_transport
    (g : Structure.Automorphism act B₀)
    {x y : β} {n : ℕ} (F : L.FuncSymbol n)
    (hy : y ∈ B₀.func F (fun _ => x)) :
    g y ∈
      B₀.func (act.onFunc g.lang F) (fun _ => g x) :=
  (baseFunction_mem_transport_iff act B₀ g F).2 hy

/-- Function fibres of the faithful witness on a constant tuple have the
literal presentation used by the construction. -/
theorem mem_witness_func_constant_iff
    {n : ℕ} (F : L.FuncSymbol n)
    (w z : WitnessVertex act A B₀ ψ) :
    z ∈
        (witnessStructure act A B₀ ψ).func F (fun _ => w) ↔
      ∃ (y : β)
        (hy : y ∈ B₀.func F (fun _ => w.base)),
        z = functionValueVertex act A B₀ ψ w F y hy := by
  rfl

/-- Transport carries each function-value witness vertex to the corresponding
function-value vertex of the transported valuation structure. -/
theorem functionValueVertex_transport [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    (w : WitnessVertex act A B₀ ψ)
    {n : ℕ} (F : L.FuncSymbol n)
    (y : β) (hy : y ∈ B₀.func F (fun _ => w.base)) :
    witnessEquiv act A B₀ ψ
        p g hsource htarget hcompat
        (functionValueVertex act A B₀ ψ w F y hy) =
      functionValueVertex act A B₀ ψ
        (WitnessVertex.transport act A B₀ ψ
          p g hsource htarget hcompat w)
        (act.onFunc g.lang F) (g y)
        (baseFunction_mem_transport act B₀ g F hy) := by
  rw [witnessEquiv_apply]
  apply Sigma.ext rfl
  apply heq_of_eq
  have hrestrict :=
    ValuationStructure.transport_restrict
      act A B₀ ψ p g hsource htarget hcompat
      w.valuation
      (func_mem_closureAtSet B₀ F hy)
  simpa [WitnessVertex.transport, functionValueVertex,
    WitnessVertex.valuation, WitnessVertex.base] using hrestrict

/-- The lifted faithful witness permutation transports every unary
function-value set exactly. -/
theorem witnessFunction_transport [Finite β]
    (p : Structure.PartialAutomorphism act
      (witnessStructure act A B₀ ψ))
    (g : Structure.Automorphism act B₀)
    (hsource : WitnessSetGeneric act A B₀ ψ p.source)
    (htarget : WitnessSetGeneric act A B₀ ψ p.target)
    (hcompat : BaseCompatible act A B₀ ψ p g)
    {n : ℕ} (F : L.FuncSymbol n)
    (ws : Fin n → WitnessVertex act A B₀ ψ) :
    Structure.imageSet
        (witnessEquiv act A B₀ ψ
          p g hsource htarget hcompat)
        ((witnessStructure act A B₀ ψ).func F ws) =
      (witnessStructure act A B₀ ψ).func
        (act.onFunc g.lang F)
        (witnessEquiv act A B₀ ψ
          p g hsource htarget hcompat ∘ ws) := by
  let w := ws (UnaryFunctions.unaryIndex F)
  have hws : ws = fun _ => w := by
    simpa [w] using
      (UnaryFunctions.unaryTuple_eq_constant F ws)
  rw [hws]
  change
    Structure.imageSet
        (witnessEquiv act A B₀ ψ
          p g hsource htarget hcompat)
        ((witnessStructure act A B₀ ψ).func F (fun _ => w)) =
      (witnessStructure act A B₀ ψ).func
        (act.onFunc g.lang F)
        (fun _ =>
          witnessEquiv act A B₀ ψ
            p g hsource htarget hcompat w)
  ext z
  constructor
  · rintro ⟨z₀, hz₀, rfl⟩
    rw [mem_witness_func_constant_iff
      act A B₀ ψ F w z₀] at hz₀
    rcases hz₀ with ⟨y, hy, rfl⟩
    rw [mem_witness_func_constant_iff]
    refine
      ⟨g y,
        baseFunction_mem_transport act B₀ g F hy,
        ?_⟩
    exact
      functionValueVertex_transport
        act A B₀ ψ p g hsource htarget hcompat
        w F y hy
  · intro hz
    rw [mem_witness_func_constant_iff] at hz
    rcases hz with ⟨y, hy, rfl⟩
    let y₀ := g.symm y
    have hy₀ :
        y₀ ∈ B₀.func F (fun _ => w.base) := by
      apply
        (baseFunction_mem_transport_iff
          act B₀ g F).1
      simpa [y₀] using hy
    refine
      ⟨functionValueVertex act A B₀ ψ w F y₀ hy₀,
        ?_, ?_⟩
    · rw [mem_witness_func_constant_iff]
      exact ⟨y₀, hy₀, rfl⟩
    · have ht :=
        functionValueVertex_transport
          act A B₀ ψ p g hsource htarget hcompat
          w F y₀ hy₀
      simpa [y₀] using ht

end Faithful
end AllThoseEPPA
