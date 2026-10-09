import AllThoseEPPA.CycleSparseningSwitch

/-! Lift simultaneous cycle switches from valuation points to witness vertices. -/

namespace AllThoseEPPA
namespace Sparsening

universe u v
variable {L : Language.{u}} {V : Type v}
variable (B₀ : Structure L V) (E : L.RelSymbol 2)
variable (switch : Structure.BadCycleSequence B₀ E → Bool)

/-- Simultaneously switch every valuation in a one-point closure. -/
def ValuationStructure.flip {x : V}
    (W : ValuationStructure B₀ E x) :
    ValuationStructure B₀ E x := by
  refine ⟨fun y => valuationFunctionFlip B₀ E switch (W.1 y), ?_⟩
  intro y z
  change AreGeneric B₀ E
    (valuationPointFlip B₀ E switch (valuationPointAt B₀ E W.1 y))
    (valuationPointFlip B₀ E switch (valuationPointAt B₀ E W.1 z))
  exact areGeneric_flip B₀ E switch (W.2 y z)

theorem ValuationStructure.flip_flip {x : V}
    (W : ValuationStructure B₀ E x) :
    (W.flip B₀ E switch).flip B₀ E switch = W := by
  apply Subtype.ext
  funext y
  funext c
  exact bitFlip_involutive (switch c.1) (W.1 y c)

/-- A simultaneous cycle switch acts on the whole witness carrier. -/
def WitnessVertex.flip (w : WitnessVertex B₀ E) :
    WitnessVertex B₀ E :=
  ⟨w.1, w.2.flip B₀ E switch⟩

@[simp] theorem WitnessVertex.flip_base
    (w : WitnessVertex B₀ E) :
    (w.flip B₀ E switch).base B₀ E = w.base B₀ E :=
  rfl

@[simp] theorem WitnessVertex.flip_pointAt
    (w : WitnessVertex B₀ E)
    (y : B₀.closureAtSet (w.base B₀ E)) :
    (w.flip B₀ E switch).pointAt B₀ E y =
      valuationPointFlip B₀ E switch (w.pointAt B₀ E y) :=
  rfl

@[simp] theorem WitnessVertex.flip_flip
    (w : WitnessVertex B₀ E) :
    (w.flip B₀ E switch).flip B₀ E switch = w := by
  rcases w with ⟨x, W⟩
  apply Sigma.ext rfl
  exact heq_of_eq (ValuationStructure.flip_flip B₀ E switch W)

/-- Switching the witness preserves and reflects pairwise genericity. -/
theorem witnessFamilyGeneric_flip_iff
    {ι : Type*} (ws : ι → WitnessVertex B₀ E) :
    WitnessFamilyGeneric B₀ E (fun i => (ws i).flip B₀ E switch) ↔
    WitnessFamilyGeneric B₀ E ws := by
  constructor
  · intro h i j y z
    have hh := h i j y z
    change AreGeneric B₀ E
      (valuationPointFlip B₀ E switch ((ws i).pointAt B₀ E y))
      (valuationPointFlip B₀ E switch ((ws j).pointAt B₀ E z)) at hh
    exact (areGeneric_flip_iff B₀ E switch _ _).1 hh
  · intro h i j y z
    change AreGeneric B₀ E
      (valuationPointFlip B₀ E switch ((ws i).pointAt B₀ E y))
      (valuationPointFlip B₀ E switch ((ws j).pointAt B₀ E z))
    exact areGeneric_flip B₀ E switch (h i j y z)

/-- Switching commutes with restricting a valuation structure to any nested
one-point closure.  This is the key function-compatibility identity. -/
theorem ValuationStructure.flip_restrict {x y : V}
    (W : ValuationStructure B₀ E x)
    (hy : y ∈ B₀.closureAtSet x) :
    (W.flip B₀ E switch).restrict B₀ E y hy =
    (W.restrict B₀ E y hy).flip B₀ E switch := by
  apply Subtype.ext
  funext z
  rfl


end Sparsening
end AllThoseEPPA
