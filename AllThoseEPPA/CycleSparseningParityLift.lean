import AllThoseEPPA.CycleSparseningParity
import AllThoseEPPA.CycleSparseningPartialSwitch

/-!
# The indexed-cycle obstruction in the sparsening witness

No projected bad induced cycle can lift to a cycle all of whose consecutive
witness pairs are generic.  This is the local parity contradiction needed
for the edge-count part of `lem:sparsen`.
-/

namespace AllThoseEPPA
namespace Structure
namespace BadCycleSequence

universe u v
variable {L : Language.{u}} {V : Type v}
variable {A : Structure L V} {E : L.RelSymbol 2}

/-- Consecutive displayed indices are non-wrap pairs of a bad cycle. -/
theorem nonWrapPair_next
    (c : BadCycleSequence A E)
    (i : Fin c.length) (hi : i.val + 1 < c.length) :
    c.NonWrapPair (c.vertex i)
      (c.vertex ⟨i.val + 1, hi⟩) := by
  refine ⟨i, ⟨i.val + 1, hi⟩, rfl, rfl, ?_, ?_⟩
  · left
    change i.val + 1 = (i.val + 1) % c.length
    rw [Nat.mod_eq_of_lt hi]
  · left
    rfl

end BadCycleSequence
end Structure

namespace Sparsening

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}
variable (B₀ : Structure L V) (E : L.RelSymbol 2)

/-- A bad base cycle cannot be lifted through a sequence of witness vertices
whose consecutive centres (including the closing pair) are generic. -/
theorem no_generic_edges_over_bad_cycle
    (c : Structure.BadCycleSequence B₀ E)
    (ws : Fin c.length → WitnessVertex B₀ E)
    (hbase : ∀ i, (ws i).base B₀ E = c.vertex i)
    (hstep :
      ∀ (i : Fin c.length) (hi : i.val + 1 < c.length),
        AreGeneric B₀ E
          (centerValuationPoint B₀ E (ws i))
          (centerValuationPoint B₀ E (ws ⟨i.val + 1, hi⟩)))
    (hwrap :
      AreGeneric B₀ E
        (centerValuationPoint B₀ E (ws c.firstIndex))
        (centerValuationPoint B₀ E (ws c.lastIndex))) :
    False := by
  let hm (i : Fin c.length) :
      (ws i).base B₀ E ∈ c.carrier :=
    ⟨i, (hbase i).symm⟩
  let b (i : Fin c.length) : Bool :=
    centerBit B₀ E (ws i) c (hm i)
  have hbitStep :
      ∀ (i : Fin c.length) (hi : i.val + 1 < c.length),
        b i = b ⟨i.val + 1, hi⟩ := by
    intro i hi
    let j : Fin c.length := ⟨i.val + 1, hi⟩
    have hne : (ws i).base B₀ E ≠ (ws j).base B₀ E := by
      rw [hbase i, hbase j]
      intro hij
      have heq := c.injective hij
      have hv := congrArg Fin.val heq
      dsimp [j] at hv
      omega
    have h := generic_centerBits_eq_iff_nonWrap B₀ E
      (ws i) (ws j) c (hm i) (hm j) hne (hstep i hi)
    exact h.mpr (c.nonWrapPair_next i hi)
  have hne :
      (ws c.firstIndex).base B₀ E ≠
        (ws c.lastIndex).base B₀ E := by
    rw [hbase c.firstIndex, hbase c.lastIndex]
    exact c.firstVertex_ne_lastVertex
  have hclosing : b c.firstIndex ≠ b c.lastIndex := by
    intro heq
    have hiff := generic_centerBits_eq_iff_nonWrap B₀ E
      (ws c.firstIndex) (ws c.lastIndex) c
      (hm c.firstIndex) (hm c.lastIndex) hne hwrap
    have hnonwrap := hiff.mp heq
    have hwrapPair : c.WrapPair
        ((ws c.firstIndex).base B₀ E)
        ((ws c.lastIndex).base B₀ E) := by
      rw [hbase c.firstIndex, hbase c.lastIndex]
      exact (c.wrapPair_iff_ends _ _).2 (Or.inl ⟨rfl, rfl⟩)
    exact (c.nonWrapPair_not_wrap hnonwrap) hwrapPair
  have hfinal :
      b ⟨0, by omega⟩ ≠ b ⟨c.length - 1, by omega⟩ := by
    exact hclosing
  exact no_cycle_bits c.length_ge_four b hbitStep hfinal

end Sparsening
end AllThoseEPPA
