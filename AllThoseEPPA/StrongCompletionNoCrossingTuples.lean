import AllThoseEPPA.StrongCompletionTwoClosureGeometry

/-!
# Separation of relation tuples in the five-part geometry

Write L₁,R₁ for the exclusive closures and L₂,R₂ for the
vertices whose closures contain the corresponding exclusive part.
The two "active" sides are L₁∪L₂ and R₁∪R₂.

The key minimal-kernel step of Proposition 11.3 implies that
each vertex of L₁ generates l, and each vertex of R₁ generates r.
We take exactly these two obligations as explicit hypotheses,
rather than silently claiming that they have already been proved.

Under them, no closed irreducible substructure can meet both active
sides, since its closure would contain l and r with f(l)=f(r).
In particular, a realized relation tuple cannot cross the two
active sides: the closure of a relation tuple is irreducible.

This isolates a substantial and otherwise delicate part of the
five-region splitting argument from the still-open minimality step.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {V : Type w}

/-- The union L₁ ∪ L₂ of the active left parts. -/
def leftActive (A : Structure L V) (l r : V) : Set V :=
  A.leftExclusive l r ∪ A.leftAbove l r

/-- The union R₁ ∪ R₂ of the active right parts. -/
def rightActive (A : Structure L V) (l r : V) : Set V :=
  A.rightExclusive l r ∪ A.rightAbove l r

/-- If S is closed and x belongs to S, then the entire
one-point closure of x is contained in S. This general
property is independent of Γ and function arity. -/
theorem closureAtSet_subset_of_closed_of_mem
    (A : Structure L V) (S : Set V)
    (hS : A.IsClosed S)
    {x : V} (hx : x ∈ S) :
    A.closureAtSet x ⊆ S := by
  apply A.closureSet_minimal hS
  intro y hy
  have hyx : y = x := by simpa using hy
  subst y
  exact hx

namespace Homomorphism

variable {Γ : Type v} [Group Γ] {W : Type x}

/-- Conditional irreducible-separation lemma. The two
single-generator hypotheses are exactly the assertions
which the manuscript obtains using minimality of the
number of identified pairs. They are not proved here. -/
theorem no_irreducible_meets_both_active_sides
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    (S : Set V) (hS : A.IsClosed S)
    (hIrr : (A.induce S hS).IsIrreducible) :
    ¬ ((∃ z : V, z ∈ S ∧ z ∈ A.leftActive l r) ∧
       (∃ z : V, z ∈ S ∧ z ∈ A.rightActive l r)) := by
  rintro ⟨⟨x, hxS, hxAct⟩, ⟨y, hyS, hyAct⟩⟩
  have hLeftBase : l ∈ A.leftExclusive l r :=
    f.left_mem_leftExclusive_of_collision act hf hne hlr
  have hRightBase : r ∈ A.rightExclusive l r :=
    f.right_mem_rightExclusive_of_collision act hf hne hlr
  have hlCl : l ∈ A.closureAtSet x := by
    rcases hxAct with hx₁ | hx₂
    · exact hL x hx₁
    · exact hx₂.2 hLeftBase
  have hrCl : r ∈ A.closureAtSet y := by
    rcases hyAct with hy₁ | hy₂
    · exact hR y hy₁
    · exact hy₂.2 hRightBase
  have hlS : l ∈ S :=
    (A.closureAtSet_subset_of_closed_of_mem S hS hxS) hlCl
  have hrS : r ∈ S :=
    (A.closureAtSet_subset_of_closed_of_mem S hS hyS) hrCl
  exact hne ((hf S hS hIrr).1 hlS hrS hlr)

/-- Conditional relation-tuple locality used in Proposition
11.3: a realized relation tuple can never contain vertices
from BOTH L₁∪L₂ and R₁∪R₂.

Unlike a graph-only argument, the proof uses irreducibility
of the closure of the *entire relation tuple*, so it handles
relation symbols of arbitrary positive arity. -/
theorem relationTuple_cannot_cross_active_sides
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → V)
    (hRel : A.rel R xs) :
    ¬ ∃ i j : Fin n,
      xs i ∈ A.leftActive l r ∧
      xs j ∈ A.rightActive l r := by
  rintro ⟨i, j, hi, hj⟩
  let S : Set V := A.closureSet (Set.range xs)
  let hS : A.IsClosed S := A.isClosed_closureSet (Set.range xs)
  have hIrr : (A.induce S hS).IsIrreducible :=
    A.relationTupleClosure_isIrreducible R xs hRel
  have hxi : xs i ∈ S :=
    A.subset_closureSet (Set.range xs) ⟨i, rfl⟩
  have hxj : xs j ∈ S :=
    A.subset_closureSet (Set.range xs) ⟨j, rfl⟩
  exact f.no_irreducible_meets_both_active_sides
    act hf hne hlr hL hR S hS hIrr
    ⟨⟨xs i, hxi, hi⟩, ⟨xs j, hxj, hj⟩⟩

end Homomorphism
end Structure
end AllThoseEPPA
