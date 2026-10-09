import AllThoseEPPA.CycleSparseningCanonicalEmbedding

/-! Simultaneous Boolean switches on indexed induced cycles. -/

namespace AllThoseEPPA
namespace Sparsening

def bitFlip (switch b : Bool) : Bool :=
  if switch then !b else b

theorem bitFlip_involutive (switch b : Bool) :
    bitFlip switch (bitFlip switch b) = b := by
  cases switch <;> cases b <;> decide

theorem bitFlip_eq_iff (switch b c : Bool) :
    bitFlip switch b = bitFlip switch c ↔ b = c := by
  cases switch <;> cases b <;> cases c <;> decide

theorem bitFlip_ne_iff (switch b c : Bool) :
    bitFlip switch b ≠ bitFlip switch c ↔ b ≠ c := by
  cases switch <;> cases b <;> cases c <;> decide

/-- A global switch acts on all indexed bad cycles through a vertex. -/
def valuationFunctionFlip
    {L : Language} {V : Type*}
    (B₀ : Structure L V) (E : L.RelSymbol 2)
    (switch : Structure.BadCycleSequence B₀ E → Bool)
    {x : V} (χ : ValuationFunction B₀ E x) :
    ValuationFunction B₀ E x :=
  fun c => bitFlip (switch c.1) (χ c)

/-- Apply the same global switch to an entire valuation point. -/
def valuationPointFlip
    {L : Language} {V : Type*}
    (B₀ : Structure L V) (E : L.RelSymbol 2)
    (switch : Structure.BadCycleSequence B₀ E → Bool)
    (p : ValuationPoint B₀ E) : ValuationPoint B₀ E :=
  ⟨p.1, valuationFunctionFlip B₀ E switch p.2⟩

@[simp] theorem valuationPointFlip_base
    {L : Language} {V : Type*}
    (B₀ : Structure L V) (E : L.RelSymbol 2)
    (switch : Structure.BadCycleSequence B₀ E → Bool)
    (p : ValuationPoint B₀ E) :
    (valuationPointFlip B₀ E switch p).1 = p.1 :=
  rfl

@[simp] theorem valuationPointFlip_flip
    {L : Language} {V : Type*}
    (B₀ : Structure L V) (E : L.RelSymbol 2)
    (switch : Structure.BadCycleSequence B₀ E → Bool)
    (p : ValuationPoint B₀ E) :
    valuationPointFlip B₀ E switch
        (valuationPointFlip B₀ E switch p) = p := by
  apply Sigma.ext rfl
  apply heq_of_eq
  funext c
  exact bitFlip_involutive (switch c.1) (p.2 c)


end Sparsening
end AllThoseEPPA
