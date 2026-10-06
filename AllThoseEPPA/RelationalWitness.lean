import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import AllThoseEPPA.EPPA

/-!
# Valuation witness for relational Γ_L-structures

This is the witness construction and generic copy from Section
`sec:relstructures` of the paper.

An `R`-valuation for a vertex `x` is mathematically defined only on tuples
containing `x`.  We represent it by a total Boolean function and require it
to be `false` off that domain.  Thus Lean equality of valuation vertices
coincides with the mathematical equality used in the paper.
-/

namespace AllThoseEPPA
namespace Relational

universe u v w

variable {L : Language.{u}}

/-- A valuation vertex `(x, χ)` for a relational language. -/
@[ext] structure WitnessVertex (L : Language.{u}) (α : Type v) where
  base : α
  valuation :
    (R : L.AnyRelSymbol) → (Fin R.1 → α) → Bool
  off_support_false :
    ∀ (R : L.AnyRelSymbol) (xs : Fin R.1 → α),
      (∀ i, xs i ≠ base) → valuation R xs = false

namespace WitnessVertex

variable {α : Type v}

/-- Base tuple underlying a tuple of valuation vertices. -/
def bases {n : ℕ} (xs : Fin n → WitnessVertex L α) : Fin n → α :=
  fun i => (xs i).base

/-- Index `i` is the first occurrence of its base vertex in a tuple. -/
def IsFirstBase {n : ℕ} (xs : Fin n → WitnessVertex L α) (i : Fin n) : Prop :=
  ∀ j, j < i → (xs j).base ≠ (xs i).base

/-- Repeated occurrences of the same base vertex must carry the same
valuation, exactly as in the definition of the witness relation in the paper. -/
def TupleCompatible {n : ℕ} (xs : Fin n → WitnessVertex L α) : Prop :=
  ∀ i j, (xs i).base = (xs j).base → xs i = xs j

/-- The first occurrences whose valuations contribute `1` to an `R`-tuple.
Using first occurrences is equivalent to summing over distinct valuation
vertices once, provided `TupleCompatible` holds. -/
noncomputable def activeIndices {n : ℕ} (R : L.RelSymbol n)
    (xs : Fin n → WitnessVertex L α) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i =>
    IsFirstBase xs i ∧
      (xs i).valuation ⟨n, R⟩ (bases xs) = true

/-- Interpretation of a relation symbol in the valuation witness. -/
noncomputable def RelationHolds {n : ℕ} (R : L.RelSymbol n)
    (xs : Fin n → WitnessVertex L α) : Prop :=
  TupleCompatible xs ∧ (activeIndices R xs).card % 2 = 1

end WitnessVertex

/-- A concrete `Fintype` instance for finite relational witnesses.
The hypothesis `Finite L.AnyRelSymbol` means that the total set of relation
symbols, across all arities, is finite. -/
noncomputable instance witnessVertexFintype
    {α : Type v} [Fintype α] [Finite L.AnyRelSymbol] :
    Fintype (WitnessVertex L α) := by
  classical
  letI : Fintype L.AnyRelSymbol := Fintype.ofFinite _
  let ValuationPoint := Σ R : L.AnyRelSymbol, (Fin R.1 → α)
  letI : Fintype ValuationPoint := by
    infer_instance
  let Code := α × (ValuationPoint → Bool)
  letI : Fintype Code := by
    infer_instance
  exact Fintype.ofInjective
    (fun v : WitnessVertex L α =>
      (v.base, fun q : ValuationPoint => v.valuation q.1 q.2))
    (by
      intro a b h
      apply WitnessVertex.ext
      · exact congrArg Prod.fst h
      · funext R xs
        have hv := congrArg Prod.snd h
        exact congrFun hv ⟨R, xs⟩)

variable [L.IsRelational]

/-- The relational valuation witness on the base set `α`.
It depends on the language and the base set, but not on the particular
relations of the input structure. -/
noncomputable def witnessStructure (α : Type v) :
    Structure L (WitnessVertex L α) where
  rel := WitnessVertex.RelationHolds
  func := by
    intro n F xs
    exact isEmptyElim F

section GenericCopy

variable {Γ : Type w} [Group Γ]
variable (act : L.Action Γ)
variable {α : Type v}
variable (A : Structure L α)

/-- The generic valuation row for base vertex `x`: it is `1` precisely
when the tuple belongs to `R^A` and `x` is its first coordinate. -/
noncomputable def genericValuation (x : α)
    (R : L.AnyRelSymbol) (xs : Fin R.1 → α) : Bool := by
  classical
  exact decide (A.rel R.2 xs ∧ x = xs (Language.firstIndex R.2))

@[simp] theorem genericValuation_eq_true_iff (x : α)
    (R : L.AnyRelSymbol) (xs : Fin R.1 → α) :
    genericValuation A x R xs = true ↔
      A.rel R.2 xs ∧ x = xs (Language.firstIndex R.2) := by
  classical
  simp [genericValuation]

/-- The generic-copy valuation vertex corresponding to `x`. -/
noncomputable def genericVertex (x : α) : WitnessVertex L α where
  base := x
  valuation := genericValuation A x
  off_support_false := by
    intro R xs hmiss
    classical
    unfold genericValuation
    apply Bool.decide_false
    intro h
    exact hmiss (Language.firstIndex R.2) h.2.symm

@[simp] theorem genericVertex_base (x : α) :
    (genericVertex A x).base = x :=
  rfl

@[simp] theorem genericVertex_valuation (x : α)
    (R : L.AnyRelSymbol) (xs : Fin R.1 → α) :
    (genericVertex A x).valuation R xs =
      genericValuation A x R xs :=
  rfl


@[simp] theorem bases_genericVertex {n : ℕ} (xs : Fin n → α) :
    WitnessVertex.bases (fun i => genericVertex A (xs i)) = xs := by
  funext i
  rfl



theorem genericTupleCompatible {n : ℕ} (xs : Fin n → α) :
    WitnessVertex.TupleCompatible (fun i => genericVertex A (xs i)) := by
  intro i j h
  have hij : xs i = xs j := by
    simpa [genericVertex] using h
  exact congrArg (genericVertex A) hij

private theorem generic_activeIndices_eq_empty {n : ℕ}
    (R : L.RelSymbol n) (xs : Fin n → α)
    (hA : ¬ A.rel R xs) :
    WitnessVertex.activeIndices R (fun i => genericVertex A (xs i)) = ∅ := by
  classical
  ext i
  simp [WitnessVertex.activeIndices, genericValuation,
    bases_genericVertex, hA]

private theorem generic_activeIndices_eq_singleton {n : ℕ}
    (R : L.RelSymbol n) (xs : Fin n → α)
    (hA : A.rel R xs) :
    WitnessVertex.activeIndices R (fun i => genericVertex A (xs i)) =
      {Language.firstIndex R} := by
  classical
  let i0 : Fin n := Language.firstIndex R
  ext i
  simp only [WitnessVertex.activeIndices, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hfirst, hval⟩
    have hbase : xs i = xs i0 := by
      have hv :=
        (genericValuation_eq_true_iff A (xs i) ⟨n, R⟩
          (WitnessVertex.bases (fun j => genericVertex A (xs j)))).1 hval
      simpa [i0] using hv.2
    apply Fin.ext
    change i.val = 0
    apply Nat.eq_zero_of_not_pos
    intro hi
    have hi0i : i0 < i := by
      change 0 < i.val
      exact hi
    have hne := hfirst i0 hi0i
    change xs i0 ≠ xs i at hne
    exact hne hbase.symm
  · intro hi
    subst i
    constructor
    · intro j hj
      exfalso
      exact Nat.not_lt_zero j.val hj
    · apply (genericValuation_eq_true_iff A (xs i0) ⟨n, R⟩
        (WitnessVertex.bases (fun j => genericVertex A (xs j)))).2
      constructor
      · simpa using hA
      · simp [i0]

/-- The generic tuple is in the witness relation exactly when the original
tuple is in the corresponding relation of `A`. -/
theorem witness_rel_generic_iff {n : ℕ}
    (R : L.RelSymbol n) (xs : Fin n → α) :
    (witnessStructure (L := L) α).rel R
        (fun i => genericVertex A (xs i)) ↔
      A.rel R xs := by
  classical
  constructor
  · rintro ⟨_, hodd⟩
    by_contra hA
    have hempty := generic_activeIndices_eq_empty A R xs hA
    rw [hempty] at hodd
    simp at hodd
  · intro hA
    refine ⟨genericTupleCompatible A xs, ?_⟩
    have hsingle := generic_activeIndices_eq_singleton A R xs hA
    rw [hsingle]
    simp

/-- The paper's generic embedding `ψ : A → B`. -/
noncomputable def genericEmbedding :
    Structure.Embedding act A (witnessStructure (L := L) α) where
  lang := 1
  toFun := genericVertex A
  injective := by
    intro x y h
    exact congrArg WitnessVertex.base h
  map_rel_iff := by
    intro n R xs
    rw [Language.Action.onRel_one act R]
    exact witness_rel_generic_iff A R xs
  map_func := by
    intro n F xs
    exact isEmptyElim F

@[simp] theorem genericEmbedding_apply (x : α) :
    genericEmbedding act A x = genericVertex A x :=
  rfl

end GenericCopy

end Relational
end AllThoseEPPA
