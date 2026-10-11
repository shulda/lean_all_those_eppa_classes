import AllThoseEPPA.Examples.IntegerMetricBasic

/-!
# Canonical shortest-path completion of symmetric positive edge costs

An arbitrary symmetric cost matrix need not satisfy the triangle
inequality. Nevertheless, when all off-diagonal entries are positive
and bounded by D, taking minimum walk length produces a genuine
integer metric of diameter at most D, on the SAME carrier.

The proof is deliberately independent of finiteness of the carrier:
the set of natural-valued walk lengths is nonempty (there is always
a direct one-edge walk), hence has a least element by well-ordering.
Walks permit repeated vertices, but a step never stays at a vertex,
so positive weights cannot create distinct points at distance zero.

This is the canonical metric completion operator needed by the
uniform EPPA regression. Additional work must prove that, under
local consistency, it PRESERVES specified relational edge lengths,
and that it transports relational automorphisms equivariantly.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

/-- Positive symmetric candidate distances, with zero diagonal.
They may violate the triangle inequality. -/
structure SymmetricCost (D : ℕ) (V : Type u) where
  cost : V → V → ℕ
  cost_self : ∀ x, cost x x = 0
  cost_pos : ∀ {x y}, x ≠ y → 0 < cost x y
  cost_symm : ∀ x y, cost x y = cost y x
  cost_le : ∀ x y, cost x y ≤ D

/-- A finite walk that only takes nontrivial steps.
Any two distinct vertices can be joined in one step. -/
inductive Walk (V : Type u) : V → V → Type u where
  | nil (x : V) : Walk V x x
  | step {x y z : V} (hxy : x ≠ y) (tail : Walk V y z) :
      Walk V x z

namespace Walk

/-- Add the cost of each step along the walk. -/
def weight {D : ℕ} {V : Type u} {x y : V}
    (p : Walk V x y) (C : SymmetricCost D V) : ℕ :=
  match p with
  | .nil _ => 0
  | .step (x := a) (y := b) _ tail =>
      C.cost a b + weight tail C

/-- Concatenation of two walks with a common endpoint. -/
def append {V : Type u} {x y z : V}
    (p : Walk V x y) (q : Walk V y z) : Walk V x z :=
  match p with
  | .nil _ => q
  | .step h tail => .step h (append tail q)

/-- Concatenating walks adds their lengths exactly. -/
theorem weight_append {D : ℕ} {V : Type u}
    (C : SymmetricCost D V) {x y z : V}
    (p : Walk V x y) (q : Walk V y z) :
    (p.append q).weight C = p.weight C + q.weight C := by
  induction p with
  | nil x => simp [append, weight]
  | step h tail ih =>
      simp [append, weight, ih, Nat.add_assoc]

/-- Traverse a walk in the opposite direction. -/
def reverse {V : Type u} {x y : V}
    (p : Walk V x y) : Walk V y x :=
  match p with
  | .nil a => .nil a
  | .step (x := a) (y := b) h tail =>
      (reverse tail).append (.step h.symm (.nil a))

/-- Symmetric edge costs make reversal preserve the total weight. -/
theorem weight_reverse {D : ℕ} {V : Type u}
    (C : SymmetricCost D V) {x y : V}
    (p : Walk V x y) :
    p.reverse.weight C = p.weight C := by
  induction p with
  | nil a => rfl
  | @step a b c h tail ih =>
      calc
        ((Walk.step h tail).reverse).weight C =
          tail.reverse.weight C + C.cost b a := by
            simp [reverse, weight_append, weight]
        _ = tail.weight C + C.cost a b := by
            rw [ih, C.cost_symm b a]
        _ = (Walk.step h tail).weight C := by
            simp [weight, Nat.add_comm]

/-- A walk between distinct endpoints has positive weight. -/
theorem weight_pos_of_ne {D : ℕ} {V : Type u}
    (C : SymmetricCost D V) {x y : V}
    (p : Walk V x y) (hxy : x ≠ y) :
    0 < p.weight C := by
  cases p with
  | nil a => exact (hxy rfl).elim
  | step h tail =>
      have hh := C.cost_pos h
      simp only [weight]
      omega

end Walk

namespace SymmetricCost

variable {D : ℕ} {V : Type u}

/-- Every ordered pair has at least one walk length.
If the endpoints differ, use the direct positive-cost step. -/
private theorem exists_walk_cost
    (C : SymmetricCost D V) (x y : V) :
    ∃ n : ℕ, ∃ p : Walk V x y, p.weight C = n := by
  by_cases hxy : x = y
  · subst y
    exact ⟨0, Walk.nil x, rfl⟩
  · refine ⟨C.cost x y, Walk.step hxy (Walk.nil y), ?_⟩
    simp [Walk.weight]

/-- Shortest-path distance, defined by the least natural walk cost.
The set is nonempty even when V is infinite. -/
noncomputable def shortest
    (C : SymmetricCost D V) (x y : V) : ℕ :=
  Nat.find (C.exists_walk_cost x y)

/-- The minimum is realized by an actual finite walk. -/
theorem exists_shortest_walk
    (C : SymmetricCost D V) (x y : V) :
    ∃ p : Walk V x y, p.weight C = C.shortest x y :=
  Nat.find_spec (C.exists_walk_cost x y)

/-- Every walk bounds the shortest distance from above. -/
theorem shortest_le_walk
    (C : SymmetricCost D V) {x y : V}
    (p : Walk V x y) :
    C.shortest x y ≤ p.weight C := by
  exact Nat.find_min' (C.exists_walk_cost x y)
    ⟨p, rfl⟩

theorem shortest_self
    (C : SymmetricCost D V) (x : V) :
    C.shortest x x = 0 := by
  have h := C.shortest_le_walk (Walk.nil x)
  simp only [Walk.weight] at h
  omega

theorem shortest_pos
    (C : SymmetricCost D V) {x y : V}
    (hxy : x ≠ y) :
    0 < C.shortest x y := by
  obtain ⟨p, hp⟩ := C.exists_shortest_walk x y
  have hpos := Walk.weight_pos_of_ne C p hxy
  rw [hp] at hpos
  exact hpos

theorem shortest_symm
    (C : SymmetricCost D V) (x y : V) :
    C.shortest x y = C.shortest y x := by
  obtain ⟨p, hp⟩ := C.exists_shortest_walk x y
  obtain ⟨q, hq⟩ := C.exists_shortest_walk y x
  have hle : C.shortest x y ≤ C.shortest y x := by
    have h := C.shortest_le_walk q.reverse
    rw [Walk.weight_reverse, hq] at h
    exact h
  have hge : C.shortest y x ≤ C.shortest x y := by
    have h := C.shortest_le_walk p.reverse
    rw [Walk.weight_reverse, hp] at h
    exact h
  exact Nat.le_antisymm hle hge

theorem shortest_triangle
    (C : SymmetricCost D V) (x y z : V) :
    C.shortest x z ≤ C.shortest x y + C.shortest y z := by
  obtain ⟨p, hp⟩ := C.exists_shortest_walk x y
  obtain ⟨q, hq⟩ := C.exists_shortest_walk y z
  have h := C.shortest_le_walk (p.append q)
  rw [Walk.weight_append, hp, hq] at h
  exact h

/-- The shortest path cannot exceed the direct input cost. -/
theorem shortest_le_cost
    (C : SymmetricCost D V) (x y : V) :
    C.shortest x y ≤ C.cost x y := by
  by_cases hxy : x = y
  · subst y
    simp [C.shortest_self, C.cost_self]
  · have h := C.shortest_le_walk
      (Walk.step hxy (Walk.nil y))
    simpa [Walk.weight] using h

/-- Canonical conversion from bounded symmetric positive costs
to a genuine bounded integer metric on the same carrier. -/
noncomputable def completedMetric
    (C : SymmetricCost D V) : BoundedNatMetric D V where
  dist := C.shortest
  dist_self := C.shortest_self
  eq_of_dist_eq_zero := by
    intro x y hzero
    by_contra hxy
    have hpos := C.shortest_pos hxy
    omega
  dist_symm := C.shortest_symm
  dist_triangle := C.shortest_triangle
  dist_le := by
    intro x y
    exact (C.shortest_le_cost x y).trans (C.cost_le x y)

end SymmetricCost
end IntegerMetric
end AllThoseEPPA
