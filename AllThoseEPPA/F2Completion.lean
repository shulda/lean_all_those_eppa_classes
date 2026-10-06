import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Linear completion of partial flip data over 𝔽₂

The relational EPPA construction prescribes flip bits on vertices that are
already in the source of a partial automorphism.  The remaining degree of
freedom is used to force even total parity: if the prescribed sum is nonzero,
the same bit is added at the first tuple entry outside the source.

With `Bool` carrying its Boolean-ring structure, addition is XOR.  Thus this
operation is literally linear over the additive group of the two-element
field.
-/

namespace AllThoseEPPA
namespace F2Completion

universe u

variable {α : Type u}

/-- Index `i` is the first occurrence of the value `xs i`. -/
def IsFirstValue {n : ℕ} (xs : Fin n → α) (i : Fin n) : Prop :=
  ∀ j, j < i → xs j ≠ xs i

/-- Representatives of the distinct values in a finite tuple. -/
noncomputable def representatives {n : ℕ}
    (xs : Fin n → α) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (IsFirstValue xs)

/-- Representatives whose values lie in the distinguished source set. -/
noncomputable def sourceRepresentatives
    (D : Set α) {n : ℕ} (xs : Fin n → α) : Finset (Fin n) := by
  classical
  exact (representatives xs).filter fun i => xs i ∈ D

/-- Sum of prescribed correction bits on distinct source values. -/
noncomputable def sourceParity
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (c : α → Bool) : Bool := by
  classical
  exact ∑ i ∈ sourceRepresentatives D xs, c (xs i)

/-- The least tuple index whose value lies outside `D`. -/
noncomputable def firstOutsideIndex
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (h : ∃ i, xs i ∉ D) : Fin n := by
  classical
  exact Fin.find (fun i => xs i ∉ D) h

theorem firstOutsideIndex_not_mem
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (h : ∃ i, xs i ∉ D) :
    xs (firstOutsideIndex D xs h) ∉ D := by
  classical
  exact Fin.find_spec h

/-- Extend prescribed source corrections to an even-parity correction:
source values keep their prescribed bits; if the tuple contains an outside
value, its first outside value receives the total source parity. -/
noncomputable def evenCompletion
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (c : α → Bool) (x : α) : Bool := by
  classical
  if hx : x ∈ D then
    exact c x
  else if h : ∃ i, xs i ∉ D then
    exact if x = xs (firstOutsideIndex D xs h) then
      sourceParity D xs c
    else false
  else
    exact false

@[simp] theorem evenCompletion_of_mem
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (c : α → Bool) {x : α} (hx : x ∈ D) :
    evenCompletion D xs c x = c x := by
  classical
  simp [evenCompletion, hx]

theorem evenCompletion_of_not_mem
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (c : α → Bool) {x : α} (hx : x ∉ D)
    (h : ∃ i, xs i ∉ D) :
    evenCompletion D xs c x =
      if x = xs (firstOutsideIndex D xs h) then
        sourceParity D xs c
      else false := by
  classical
  simp [evenCompletion, hx, h]

theorem sourceParity_add
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (c₁ c₂ : α → Bool) :
    sourceParity D xs (fun x => c₁ x + c₂ x) =
      sourceParity D xs c₁ + sourceParity D xs c₂ := by
  classical
  simp [sourceParity, Finset.sum_add_distrib]

/-- The parity completion is linear in the prescribed correction vector. -/
theorem evenCompletion_add
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (c₁ c₂ : α → Bool) (x : α) :
    evenCompletion D xs (fun y => c₁ y + c₂ y) x =
      evenCompletion D xs c₁ x + evenCompletion D xs c₂ x := by
  classical
  by_cases hx : x ∈ D
  · simp [evenCompletion, hx]
  · by_cases h : ∃ i, xs i ∉ D
    · by_cases heq : x = xs (firstOutsideIndex D xs h)
      · simp [evenCompletion, hx, h, heq, sourceParity_add]
      · simp [evenCompletion, hx, h, heq]
    · simp [evenCompletion, hx, h]

end F2Completion
end AllThoseEPPA
