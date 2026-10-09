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

end Sparsening
end AllThoseEPPA
