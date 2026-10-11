import AllThoseEPPA.StrongCompletionNoCrossingTuples

/-!
# Irreducibles in unary-function languages are primitively pair-supported

Let A have only unary set-valued functions. For any two vertices
x,y of an irreducible A, either

* some vertex z generates both x and y in its unary-function
  closure, or
* some realized relation tuple has a functionally generated
  closure containing x and y.

This is a useful strengthening of the simple fact that every
one-point closure and every relation-tuple closure is irreducible.

The proof is a structural contrapositive. If the two vertices
are never generated together, split A into the closed sides

  left  = {z : x ∉ Cl(z)},
  right = {z : y ∉ Cl(z)}.

They cover A and are proper. Unary function values preserve
both sides. A relation tuple crossing the two sides would
generate both x and y, contradicting the premise; mixed
function tuples are impossible because the functions are unary.

Consequently the split is a genuine FreeDecomposition, which
an irreducible structure forbids. The argument does not
require finiteness, trivial Γ action, or a restriction on
relation arities.

This theorem is designed for the remaining target-side
homomorphism-embedding obligation of Proposition 11.3:
it reduces collisions inside irreducibles to collisions
within explicitly generated primitive pieces.
-/

namespace AllThoseEPPA
namespace Structure

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {V : Type v}

/-- Two vertices have a common **primitive support** if a
single one-point closure or one realized relation tuple
generates both of them. -/
def PrimitivePairWitness (A : Structure L V) (x y : V) : Prop :=
  (∃ z : V, x ∈ A.closureAtSet z ∧ y ∈ A.closureAtSet z) ∨
  (∃ (n : ℕ) (R : L.RelSymbol n) (xs : Fin n → V),
      A.rel R xs ∧
      x ∈ A.closureSet (Set.range xs) ∧
      y ∈ A.closureSet (Set.range xs))

/-- In a unary-function language, a failure of primitive
pair support induces an explicit free decomposition.

The free cut is not only a graph-level partition: its
closedness and the absence of mixed function fibres are
verified in the full set-valued-function language. -/
noncomputable def freeDecomposition_of_not_primitivePairWitness
    (A : Structure L V) (x y : V)
    (hNo : ¬ A.PrimitivePairWitness x y) :
    A.FreeDecomposition := by
  classical
  let left : Set V := {z | x ∉ A.closureAtSet z}
  let right : Set V := {z | y ∉ A.closureAtSet z}
  have hCover : left ∪ right = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hx : x ∈ A.closureAtSet z
    · have hy : y ∉ A.closureAtSet z := by
        intro hy
        exact hNo (Or.inl ⟨z, hx, hy⟩)
      exact Or.inr hy
    · exact Or.inl hx
  have hLeftClosed : A.IsClosed left := by
    intro n F xs hxs t ht
    have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
    subst n
    have htClosure : t ∈ A.closureAtSet (xs 0) := by
      apply (A.isClosed_closureSet {xs 0}) F xs
      · intro i
        have hi : i = 0 := Subsingleton.elim i 0
        subst i
        exact A.mem_closureAtSet (xs 0)
      · exact ht
    have hSub : A.closureAtSet t ⊆ A.closureAtSet (xs 0) :=
      A.closureAtSet_subset_of_mem htClosure
    intro hx
    exact (hxs 0) (hSub hx)
  have hRightClosed : A.IsClosed right := by
    intro n F xs hxs t ht
    have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
    subst n
    have htClosure : t ∈ A.closureAtSet (xs 0) := by
      apply (A.isClosed_closureSet {xs 0}) F xs
      · intro i
        have hi : i = 0 := Subsingleton.elim i 0
        subst i
        exact A.mem_closureAtSet (xs 0)
      · exact ht
    have hSub : A.closureAtSet t ⊆ A.closureAtSet (xs 0) :=
      A.closureAtSet_subset_of_mem htClosure
    intro hy
    exact (hxs 0) (hSub hy)
  have hLeftProper : left ≠ Set.univ := by
    intro hAll
    have hx : x ∈ left := by rw [hAll]; exact Set.mem_univ _
    exact hx (A.mem_closureAtSet x)
  have hRightProper : right ≠ Set.univ := by
    intro hAll
    have hy : y ∈ right := by rw [hAll]; exact Set.mem_univ _
    exact hy (A.mem_closureAtSet y)
  refine {
    left := left
    right := right
    left_closed := hLeftClosed
    right_closed := hRightClosed
    cover := hCover
    left_proper := hLeftProper
    right_proper := hRightProper
    rel_local := ?_
    func_cross_empty := ?_ }
  · intro n R xs hRel
    by_contra hNoSide
    have hNotLeft : ¬ ∀ i, xs i ∈ left := by
      intro hAll
      exact hNoSide (Or.inl hAll)
    have hNotRight : ¬ ∀ i, xs i ∈ right := by
      intro hAll
      exact hNoSide (Or.inr hAll)
    obtain ⟨i, hi⟩ := Classical.not_forall.mp hNotLeft
    obtain ⟨j, hj⟩ := Classical.not_forall.mp hNotRight
    have hxi : x ∈ A.closureAtSet (xs i) := by
      exact not_not.mp hi
    have hyj : y ∈ A.closureAtSet (xs j) := by
      exact not_not.mp hj
    have hxs_i : xs i ∈ A.closureSet (Set.range xs) :=
      A.subset_closureSet (Set.range xs) ⟨i, rfl⟩
    have hxs_j : xs j ∈ A.closureSet (Set.range xs) :=
      A.subset_closureSet (Set.range xs) ⟨j, rfl⟩
    have hx : x ∈ A.closureSet (Set.range xs) :=
      (A.closureAtSet_subset_of_closed_of_mem
        (A.closureSet (Set.range xs))
        (A.isClosed_closureSet (Set.range xs)) hxs_i) hxi
    have hy : y ∈ A.closureSet (Set.range xs) :=
      (A.closureAtSet_subset_of_closed_of_mem
        (A.closureSet (Set.range xs))
        (A.isClosed_closureSet (Set.range xs)) hxs_j) hyj
    exact hNo (Or.inr ⟨n, R, xs, hRel, hx, hy⟩)
  · intro n F xs hCross
    have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
    subst n
    have hSide : xs 0 ∈ left ∪ right := by
      rw [hCover]
      exact Set.mem_univ _
    have hFalse : False := by
      rcases hSide with hL | hR
      · apply hCross
        left
        intro i
        have hi : i = 0 := Subsingleton.elim i 0
        subst i
        exact hL
      · apply hCross
        right
        intro i
        have hi : i = 0 := Subsingleton.elim i 0
        subst i
        exact hR
    exact hFalse.elim

/-- **Primitive pair-witness theorem** for irreducible
structures with unary set-valued functions.

For every two vertices of A, there exists a single
one-point closure or a single realized relation-tuple
closure containing both vertices. -/
theorem IsIrreducible.primitivePairWitness
    (A : Structure L V)
    (hIrr : A.IsIrreducible)
    (x y : V) :
    A.PrimitivePairWitness x y := by
  by_contra hNo
  exact hIrr.false
    (A.freeDecomposition_of_not_primitivePairWitness x y hNo)

end Structure
end AllThoseEPPA
