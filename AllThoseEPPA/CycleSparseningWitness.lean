import AllThoseEPPA.CycleSparseningGeneric
import AllThoseEPPA.UnaryFunctions

/-!
# Valuation structures and witness vertices for cycle sparsening

This is the normalized data layer of the construction in Section `sec:cycles`.
As in the faithful construction, a valuation structure over `x` is represented
by one valuation function above every point of the one-point closure of `x`,
subject to pairwise genericity.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v

variable {L : Language.{u}}
variable {V : Type v}
variable (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- A cycle-valuation assignment over the one-point closure of a base point. -/
abbrev ValuationAssignment (x : V) :=
  ∀ y : B₀.closureAtSet x,
    ValuationFunction B₀ E y.1

/-- The valuation point selected at a member of a one-point closure. -/
def valuationPointAt
    {x : V} (v : ValuationAssignment B₀ E x)
    (y : B₀.closureAtSet x) :
    ValuationPoint B₀ E :=
  ⟨y.1, v y⟩

/-- Pairwise genericity of all valuation points in an assignment. -/
def IsGenericAssignment
    {x : V} (v : ValuationAssignment B₀ E x) : Prop :=
  ∀ y z : B₀.closureAtSet x,
    AreGeneric B₀ E
      (valuationPointAt B₀ E v y)
      (valuationPointAt B₀ E v z)

/-- A valuation structure over `x`, normalized to the data relevant for the
cycle construction. -/
abbrev ValuationStructure (x : V) :=
  {v : ValuationAssignment B₀ E x //
    IsGenericAssignment B₀ E v}

/-- Inclusion of a nested one-point closure into the ambient one. -/
def closureInclusion
    {x y : V} (hy : y ∈ B₀.closureAtSet x)
    (z : B₀.closureAtSet y) :
    B₀.closureAtSet x :=
  ⟨z.1, B₀.closureAtSet_subset_of_mem hy z.2⟩

/-- Restriction of a valuation structure to the closure of one of its points. -/
def ValuationStructure.restrict
    {x : V} (W : ValuationStructure B₀ E x)
    (y : V) (hy : y ∈ B₀.closureAtSet x) :
    ValuationStructure B₀ E y :=
  ⟨fun z => W.1 (closureInclusion B₀ hy z),
    by
      intro z z'
      exact W.2
        (closureInclusion B₀ hy z)
        (closureInclusion B₀ hy z')⟩

/-- Vertices of the cycle-sparsening witness. -/
abbrev WitnessVertex :=
  Σ x : V, ValuationStructure B₀ E x

namespace WitnessVertex

def base
    (w : WitnessVertex B₀ E) : V :=
  w.1

def valuation
    (w : WitnessVertex B₀ E) :
    ValuationStructure B₀ E (base B₀ E w) :=
  w.2

/-- The valuation point of a witness vertex at a point of its one-point
closure. -/
def pointAt
    (w : WitnessVertex B₀ E)
    (y : B₀.closureAtSet (base B₀ E w)) :
    ValuationPoint B₀ E :=
  valuationPointAt B₀ E (valuation B₀ E w).1 y

end WitnessVertex

/-- A family of witness vertices is generic when the union of the valuation
structures carried by them is pairwise generic. -/
def WitnessFamilyGeneric
    {ι : Type*} (ws : ι → WitnessVertex B₀ E) : Prop :=
  ∀ i j
      (y : B₀.closureAtSet (WitnessVertex.base B₀ E (ws i)))
      (z : B₀.closureAtSet (WitnessVertex.base B₀ E (ws j))),
    AreGeneric B₀ E
      (WitnessVertex.pointAt B₀ E (ws i) y)
      (WitnessVertex.pointAt B₀ E (ws j) z)

/-- Function values at a constant tuple lie in the one-point closure of the
constant vertex. -/
theorem func_mem_closureAtSet
    {x y : V} {n : ℕ} (F : L.FuncSymbol n)
    (hy : y ∈ B₀.func F (fun _ => x)) :
    y ∈ B₀.closureAtSet x := by
  change y ∈ B₀.closureSet {x}
  exact
    (B₀.isClosed_closureSet ({x} : Set V))
      F (fun _ => x) (fun _ => B₀.mem_closureAtSet x) hy

/-- Witness vertex attached to a unary function value. -/
def functionValueVertex
    (w : WitnessVertex B₀ E)
    {n : ℕ} (F : L.FuncSymbol n)
    (y : V)
    (hy : y ∈ B₀.func F
      (fun _ => WitnessVertex.base B₀ E w)) :
    WitnessVertex B₀ E :=
  ⟨y,
    (WitnessVertex.valuation B₀ E w).restrict B₀ E y
      (func_mem_closureAtSet B₀ F hy)⟩

section UnaryWitness

variable [L.HasUnaryFunctions]

/-- The normalized witness structure for the cycle-sparsening construction. -/
noncomputable def witnessStructure :
    Structure L (WitnessVertex B₀ E) where
  rel := by
    intro n R ws
    exact
      B₀.rel R
          (fun i => WitnessVertex.base B₀ E (ws i)) ∧
        WitnessFamilyGeneric B₀ E ws
  func := by
    intro n F ws
    let w := ws (UnaryFunctions.unaryIndex F)
    exact
      {z | ∃ (y : V)
        (hy : y ∈ B₀.func F
          (fun _ => WitnessVertex.base B₀ E w)),
        z = functionValueVertex B₀ E w F y hy}

end UnaryWitness

end Sparsening
end AllThoseEPPA
