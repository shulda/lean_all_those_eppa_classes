import AllThoseEPPA.StrongCompletionLocalCollapse

/-!
# Unary function-fibre compatibility of the local closure collapse

The generic quotient q:A→q₊A can only be an exact
homomorphism-embedding if the existential pushforward does not
add new function values to tuples from a closed irreducible
source piece.

For the special local collapse of Cl(b) onto Cl(a), this
compatibility DOES follow from unarity:

* function outputs lie in the one-point closure of their input;
* if q(x)=q(y) and x≠y, then x,y lie in opposite matched
  one-point closures;
* outputs from opposite closures having the same f-value are
  collapsed onto the same representative.

We prove the complete quantified compatibility property here,
without assuming it as an axiom. Once the generic pushforward
criterion is integrated, this supplies exact source-side
function-fibre preservation for the quotient.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- If s is in the right one-point closure and t in the left
one-point closure, equal f-values imply equal collapse images. -/
theorem collapseRightClosure_eq_of_cross_same_f
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b)
    {s t : V} (hs : s ∈ A.closureAtSet b)
    (ht : t ∈ A.closureAtSet a)
    (hst : f s = f t) :
    f.collapseRightClosure act hf hab s =
      f.collapseRightClosure act hf hab t := by
  have hqt : f.collapseRightClosure act hf hab t = t :=
    f.collapseRightClosure_fixes_left act hf hab ht
  by_cases hsLeft : s ∈ A.closureAtSet a
  · have hqs : f.collapseRightClosure act hf hab s = s :=
      f.collapseRightClosure_fixes_left act hf hab hsLeft
    rw [hqs, hqt]
    exact (f.injOn_closureAt act hf a) hsLeft ht hst
  · have hsRight : s ∈ A.rightExclusive a b :=
      ⟨hs, hsLeft⟩
    have hqsLeft :
        f.collapseRightClosure act hf hab s ∈ A.closureAtSet a :=
      f.collapseRightClosure_mem_left act hf hab hsRight
    have hEqualValues :
        f (f.collapseRightClosure act hf hab s) = f t :=
      (f.collapseRightClosure_preserves_f act hf hab s).trans hst
    have hqs : f.collapseRightClosure act hf hab s = t :=
      (f.injOn_closureAt act hf a) hqsLeft ht hEqualValues
    rw [hqs, hqt]

/-- Any value of a genuinely set-valued UNARY function
belongs to the one-point closure of the unique input. -/
theorem unary_function_value_mem_closure
    (A : Structure L V)
    (F : L.FuncSymbol 1)
    (xs : Fin 1 → V)
    {z : V} (hz : z ∈ A.func F xs) :
    z ∈ A.closureAtSet (xs 0) := by
  apply (A.isClosed_closureSet {xs 0}) F xs
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact A.mem_closureAtSet (xs 0)
  · exact hz

/-- Unary function values remain inside any one-point
closure containing their input. -/
theorem unary_function_value_mem_parent_closure
    (A : Structure L V)
    (F : L.FuncSymbol 1) (xs : Fin 1 → V)
    {c z : V}
    (hc : xs 0 ∈ A.closureAtSet c)
    (hz : z ∈ A.func F xs) :
    z ∈ A.closureAtSet c := by
  have hval := unary_function_value_mem_closure A F xs hz
  exact A.closureAtSet_subset_of_mem hc hval

/-- The local collapse is compatible with all set-valued
unary function fibres in the exact sense needed by the
canonical existential quotient construction. -/
theorem collapseRightClosure_function_fibre_compatible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) :
    ∀ {n : ℕ} (F : L.FuncSymbol n)
      (xs ys : Fin n → V),
      (f.collapseRightClosure act hf hab) ∘ xs =
        (f.collapseRightClosure act hf hab) ∘ ys →
      ∀ (z : V), z ∈ A.func F xs →
      ∀ (t : V), t ∈ A.func F ys →
      f z = f t →
      f.collapseRightClosure act hf hab z =
        f.collapseRightClosure act hf hab t := by
  intro n F xs ys hTuples z hz t ht hzt
  have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
  subst n
  have hzCl :
      z ∈ A.closureAtSet (xs 0) :=
    unary_function_value_mem_closure A F xs hz
  have htCl :
      t ∈ A.closureAtSet (ys 0) :=
    unary_function_value_mem_closure A F ys ht
  have hqxqy :
      f.collapseRightClosure act hf hab (xs 0) =
        f.collapseRightClosure act hf hab (ys 0) :=
    congrFun hTuples 0
  by_cases hxy : xs 0 = ys 0
  · have htClX : t ∈ A.closureAtSet (xs 0) := by
      rw [hxy]
      exact htCl
    have hztEq : z = t :=
      (f.injOn_closureAt act hf (xs 0)) hzCl htClX hzt
    exact congrArg (f.collapseRightClosure act hf hab) hztEq
  · rcases
      f.collapseRightClosure_collisions_only_cross
        act hf hab hxy hqxqy with
      ⟨hxB, hyA, _⟩ | ⟨hxA, hyB, _⟩
    · have hzB : z ∈ A.closureAtSet b :=
        unary_function_value_mem_parent_closure A F xs hxB hz
      have htA : t ∈ A.closureAtSet a :=
        unary_function_value_mem_parent_closure A F ys hyA ht
      exact f.collapseRightClosure_eq_of_cross_same_f
        act hf hab hzB htA hzt
    · have hzA : z ∈ A.closureAtSet a :=
        unary_function_value_mem_parent_closure A F xs hxA hz
      have htB : t ∈ A.closureAtSet b :=
        unary_function_value_mem_parent_closure A F ys hyB ht
      exact (f.collapseRightClosure_eq_of_cross_same_f
        act hf hab htB hzA hzt.symm).symm

end Homomorphism
end Structure
end AllThoseEPPA
