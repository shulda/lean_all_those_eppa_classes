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

end Sparsening
end AllThoseEPPA
