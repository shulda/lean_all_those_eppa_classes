import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
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

open scoped BigOperators

universe u

variable {α : Type u} [DecidableEq α]

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


/-- Distinct tuple values have unique representative indices. -/
theorem representatives_injOn {n : ℕ} (xs : Fin n → α) :
    Set.InjOn xs (↑(representatives xs) : Set (Fin n)) := by
  classical
  intro i hi j hj hij
  have hfirst_i : IsFirstValue xs i :=
    (Finset.mem_filter.mp hi).2
  have hfirst_j : IsFirstValue xs j :=
    (Finset.mem_filter.mp hj).2
  rcases lt_trichotomy i j with hijlt | hEq | hjilt
  · exact (hfirst_j i hijlt hij).elim
  · exact hEq
  · exact (hfirst_i j hjilt hij.symm).elim

/-- The least outside index is the representative of its base value. -/
theorem firstOutsideIndex_mem_representatives
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (h : ∃ i, xs i ∉ D) :
    firstOutsideIndex D xs h ∈ representatives xs := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro j hj hbase
  have hjout : xs j ∉ D := by
    simpa [hbase] using firstOutsideIndex_not_mem D xs h
  exact (Fin.find_min h hj) hjout

/-- XOR over the distinct values occurring in a tuple. -/
noncomputable def totalParity {n : ℕ}
    (xs : Fin n → α) (c : α → Bool) : Bool := by
  classical
  exact ∑ i ∈ representatives xs, c (xs i)

/-- If the tuple contains a value outside `D`, parity completion lands in
the even-parity hyperplane: the total XOR over distinct tuple values is zero. -/
theorem totalParity_evenCompletion_of_exists_outside
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (c : α → Bool) (h : ∃ i, xs i ∉ D) :
    totalParity xs (evenCompletion D xs c) = false := by
  classical
  let i₀ : Fin n := firstOutsideIndex D xs h
  have hi₀rep : i₀ ∈ representatives xs := by
    exact firstOutsideIndex_mem_representatives D xs h
  have hi₀out : xs i₀ ∉ D := by
    exact firstOutsideIndex_not_mem D xs h
  have hcenter :
      evenCompletion D xs c (xs i₀) = sourceParity D xs c := by
    rw [evenCompletion_of_not_mem D xs c hi₀out h]
    simp [i₀]
  have houtsum :
      (∑ i ∈ (representatives xs).filter (fun i => xs i ∉ D),
          evenCompletion D xs c (xs i)) =
        sourceParity D xs c := by
    rw [← hcenter]
    apply Finset.sum_eq_single i₀
    · intro j hj hji
      have hjrep : j ∈ representatives xs := (Finset.mem_filter.mp hj).1
      have hjout : xs j ∉ D := (Finset.mem_filter.mp hj).2
      have hbase : xs j ≠ xs i₀ := by
        intro hb
        exact hji (representatives_injOn xs hjrep hi₀rep hb)
      rw [evenCompletion_of_not_mem D xs c hjout h]
      simp [i₀, hbase, Bool.zero_eq_false]
    · intro hi
      exact (hi (Finset.mem_filter.mpr ⟨hi₀rep, hi₀out⟩)).elim
  have hsourcesum :
      (∑ i ∈ (representatives xs).filter (fun i => xs i ∈ D),
          evenCompletion D xs c (xs i)) =
        sourceParity D xs c := by
    unfold sourceParity sourceRepresentatives
    apply Finset.sum_congr rfl
    intro i hi
    have hiD : xs i ∈ D := (Finset.mem_filter.mp hi).2
    exact evenCompletion_of_mem D xs c hiD
  unfold totalParity
  rw [← Finset.sum_filter_add_sum_filter_not
      (representatives xs) (fun i => xs i ∈ D)
      (fun i => evenCompletion D xs c (xs i))]
  rw [hsourcesum, houtsum]
  cases hsp : sourceParity D xs c <;> rfl

/-- If every tuple value lies in `D`, completion does not add a parity
coordinate and total parity is exactly the prescribed source parity. -/
theorem totalParity_evenCompletion_of_forall_mem
    (D : Set α) {n : ℕ} (xs : Fin n → α)
    (c : α → Bool) (h : ∀ i, xs i ∈ D) :
    totalParity xs (evenCompletion D xs c) =
      sourceParity D xs c := by
  classical
  have hsrc :
      sourceRepresentatives D xs = representatives xs := by
    ext i
    simp [sourceRepresentatives, h]
  unfold totalParity sourceParity
  rw [hsrc]
  apply Finset.sum_congr rfl
  intro i hi
  exact evenCompletion_of_mem D xs c (h i)

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
      · simp [evenCompletion, hx, h, heq, sourceParity_add,
          firstOutsideIndex_not_mem D xs h]
      · simp [evenCompletion, hx, h, heq, Bool.zero_eq_false]
    · simp [evenCompletion, hx, h, Bool.zero_eq_false]

end F2Completion
end AllThoseEPPA
