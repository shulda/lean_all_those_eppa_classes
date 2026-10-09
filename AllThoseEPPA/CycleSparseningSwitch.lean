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
  rcases p with ⟨x, χ⟩
  apply Sigma.ext rfl
  apply heq_of_eq
  funext c
  exact bitFlip_involutive (switch c.1) (χ c)


/-- Switching every cycle simultaneously preserves exactly the generic pairs. -/
theorem areGeneric_flip
    {L : Language} {V : Type*}
    (B₀ : Structure L V) (E : L.RelSymbol 2)
    (switch : Structure.BadCycleSequence B₀ E → Bool)
    {p q : ValuationPoint B₀ E}
    (h : AreGeneric B₀ E p q) :
    AreGeneric B₀ E
      (valuationPointFlip B₀ E switch p)
      (valuationPointFlip B₀ E switch q) := by
  rcases h with hpq | ⟨hne, hcycles⟩
  · exact Or.inl (congrArg (valuationPointFlip B₀ E switch) hpq)
  · refine Or.inr ⟨hne, ?_⟩
    intro c hp hq
    rcases hcycles c hp hq with ⟨hnw, heq⟩ | ⟨hw, hnebits⟩
    · refine Or.inl ⟨hnw, ?_⟩
      change bitFlip (switch c)
          (p.2 ⟨c, hp⟩) =
        bitFlip (switch c) (q.2 ⟨c, hq⟩)
      exact (bitFlip_eq_iff _ _ _).2 heq
    · refine Or.inr ⟨hw, ?_⟩
      change bitFlip (switch c)
          (p.2 ⟨c, hp⟩) ≠
        bitFlip (switch c) (q.2 ⟨c, hq⟩)
      exact (bitFlip_ne_iff _ _ _).2 hnebits

theorem areGeneric_flip_iff
    {L : Language} {V : Type*}
    (B₀ : Structure L V) (E : L.RelSymbol 2)
    (switch : Structure.BadCycleSequence B₀ E → Bool)
    (p q : ValuationPoint B₀ E) :
    AreGeneric B₀ E
      (valuationPointFlip B₀ E switch p)
      (valuationPointFlip B₀ E switch q) ↔
    AreGeneric B₀ E p q := by
  constructor
  · intro h
    have hh := areGeneric_flip B₀ E switch h
    simpa only [valuationPointFlip_flip] using hh
  · exact areGeneric_flip B₀ E switch


end Sparsening
end AllThoseEPPA
