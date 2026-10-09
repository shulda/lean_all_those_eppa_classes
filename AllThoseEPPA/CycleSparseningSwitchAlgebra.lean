import AllThoseEPPA.CycleSparseningSwitchWitness

/-!
# Algebra of simultaneous cycle switches

Global Boolean switching is addition in the vector space of functions
from indexed bad cycles to F₂. This is the algebraic input to the
coherent-extension composition calculation.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v
variable {L : Language.{u}} {V : Type v}
variable (B₀ : Structure L V) (E : L.RelSymbol 2)

/-- Addition of switches, i.e. pointwise XOR. -/
def switchSum
    (s t : Structure.BadCycleSequence B₀ E → Bool) :
    Structure.BadCycleSequence B₀ E → Bool :=
  fun c => s c != t c

theorem switchSum_assoc
    (s t u : Structure.BadCycleSequence B₀ E → Bool) :
    switchSum B₀ E (switchSum B₀ E s t) u =
    switchSum B₀ E s (switchSum B₀ E t u) := by
  funext c
  dsimp [switchSum]
  cases hs : s c <;> cases ht : t c <;> cases hu : u c <;>
    simp [hs, ht, hu]

theorem switchSum_comm
    (s t : Structure.BadCycleSequence B₀ E → Bool) :
    switchSum B₀ E s t = switchSum B₀ E t s := by
  funext c
  dsimp [switchSum]
  cases hs : s c <;> cases ht : t c <;>
    simp [hs, ht]

/-- Applying two flips consecutively is a single flip with XOR switch. -/
theorem bitFlip_comp (s t b : Bool) :
    bitFlip s (bitFlip t b) = bitFlip (s != t) b := by
  cases s <;> cases t <;> cases b <;> decide

theorem valuationFunctionFlip_comp
    (s t : Structure.BadCycleSequence B₀ E → Bool)
    {x : V} (χ : ValuationFunction B₀ E x) :
    valuationFunctionFlip B₀ E s (valuationFunctionFlip B₀ E t χ) =
    valuationFunctionFlip B₀ E (switchSum B₀ E s t) χ := by
  funext c
  exact bitFlip_comp (s c.1) (t c.1) (χ c)

/-- Composition law on the actual generic valuation structures. -/
theorem ValuationStructure.flip_comp
    (s t : Structure.BadCycleSequence B₀ E → Bool)
    {x : V} (W : ValuationStructure B₀ E x) :
    (W.flip B₀ E t).flip B₀ E s =
      W.flip B₀ E (switchSum B₀ E s t) := by
  apply Subtype.ext
  funext y
  exact valuationFunctionFlip_comp B₀ E s t (W.1 y)

/-- Pointwise XOR is the composition law on witness-vertex switches. -/
theorem WitnessVertex.flip_comp
    (s t : Structure.BadCycleSequence B₀ E → Bool)
    (w : WitnessVertex B₀ E) :
    (w.flip B₀ E t).flip B₀ E s =
      w.flip B₀ E (switchSum B₀ E s t) := by
  rcases w with ⟨x, W⟩
  change
    (⟨x, (W.flip B₀ E t).flip B₀ E s⟩ : WitnessVertex B₀ E) =
    ⟨x, W.flip B₀ E (switchSum B₀ E s t)⟩
  exact congrArg
    (fun Q : ValuationStructure B₀ E x =>
      (⟨x, Q⟩ : WitnessVertex B₀ E))
    (ValuationStructure.flip_comp B₀ E s t W)

end Sparsening
end AllThoseEPPA
