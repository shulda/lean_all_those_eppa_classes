import AllThoseEPPA.CycleSparseningPartialExtension
import Lean.Elab.Tactic.Omega

/-!
# Boolean parity obstruction to lifting induced cycles

A sequence of Boolean bits that is constant on all consecutive edges of
an ordered cycle cannot change value on its closing edge.  This elementary
chain lemma isolates the combinatorial contradiction at the end of the
sparsening proof.
-/

namespace AllThoseEPPA
namespace Sparsening

/-- A Boolean labelling which agrees across every consecutive pair has
the same value at the first index and at any index. -/
theorem cycleBits_eq_first
    {k : ℕ} (hk : 4 ≤ k)
    (b : Fin k → Bool)
    (hstep : ∀ (i : Fin k) (hi : i.val + 1 < k),
      b i = b ⟨i.val + 1, hi⟩)
    (j : Fin k) :
    b ⟨0, by omega⟩ = b j := by
  have hzero : 0 < k := by omega
  have h : ∀ n : ℕ, ∀ hn : n < k,
      b ⟨0, hzero⟩ = b ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      rfl
    | succ n ih =>
      intro hn
      have hn0 : n < k := by omega
      calc
        b ⟨0, hzero⟩ = b ⟨n, hn0⟩ := ih hn0
        _ = b ⟨n + 1, hn⟩ := hstep ⟨n, hn0⟩ hn
  exact h j.val j.isLt

/-- No Boolean cycle can have equal bits on its linear consecutive edges
but unequal bits on the wrap edge. -/
theorem no_cycle_bits
    {k : ℕ} (hk : 4 ≤ k)
    (b : Fin k → Bool)
    (hstep : ∀ (i : Fin k) (hi : i.val + 1 < k),
      b i = b ⟨i.val + 1, hi⟩)
    (hwrap : b ⟨0, by omega⟩ ≠ b ⟨k - 1, by omega⟩) :
    False := by
  exact hwrap (cycleBits_eq_first hk b hstep ⟨k - 1, by omega⟩)

end Sparsening
end AllThoseEPPA
