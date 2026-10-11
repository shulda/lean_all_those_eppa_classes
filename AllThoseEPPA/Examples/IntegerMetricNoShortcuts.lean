import AllThoseEPPA.Examples.IntegerMetricShortestPaths

/-!
# Exact preservation criterion and bounded short-path obstructions

For the canonical shortest-path completion, an existing candidate
distance c(x,y) is preserved **if and only if** no walk from x to y
has weight smaller than c(x,y). This is the exact local obligation
needed to preserve the prescribed colours in the metric EPPA
regression.

A cheaper walk of weight < d has fewer than d steps, because every
nontrivial step has weight at least one. Therefore a violation of a
prescribed distance d ≤ D always has a witness involving at most d
steps and hence at most d+1 visited vertices. Formalizing the actual
vertex support and its bounded-substructure completion is next.

As a sanity check, if the original cost matrix already satisfies
the triangle inequality then its shortest-path completion leaves
EVERY distance unchanged.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

namespace Walk

/-- Count the number of nontrivial steps in a walk. -/
def steps {V : Type u} {x y : V} (p : Walk V x y) : ℕ :=
  match p with
  | .nil _ => 0
  | .step _ tail => tail.steps + 1

/-- Every step has cost at least one. -/
theorem steps_le_weight {D : ℕ} {V : Type u}
    (C : SymmetricCost D V) {x y : V}
    (p : Walk V x y) :
    p.steps ≤ p.weight C := by
  induction p with
  | nil a => rfl
  | @step a b z h tail ih =>
      change tail.steps + 1 ≤ C.cost a b + tail.weight C
      have hp : 0 < C.cost a b := C.cost_pos h
      omega

/-- A walk of total weight less than d uses fewer than d steps. -/
theorem steps_lt_of_weight_lt {D : ℕ} {V : Type u}
    (C : SymmetricCost D V) {x y : V}
    (p : Walk V x y) {d : ℕ}
    (h : p.weight C < d) :
    p.steps < d :=
  (p.steps_le_weight C).trans_lt h

end Walk

namespace SymmetricCost

variable {D : ℕ} {V : Type u}

/-- Exactly when does canonical shortest-path completion keep the
given direct cost of an ordered pair? Precisely when every
walk between those vertices costs at least that much. -/
theorem shortest_eq_cost_iff_no_shortcut
    (C : SymmetricCost D V) (x y : V) :
    C.shortest x y = C.cost x y ↔
      ∀ p : Walk V x y, C.cost x y ≤ p.weight C := by
  constructor
  · intro h p
    rw [← h]
    exact C.shortest_le_walk p
  · intro h
    apply Nat.le_antisymm (C.shortest_le_cost x y)
    obtain ⟨p, hp⟩ := C.exists_shortest_walk x y
    calc
      C.cost x y ≤ p.weight C := h p
      _ = C.shortest x y := hp

/-- Triangle inequalities of the original costs imply that
every walk costs at least the original direct distance. -/
theorem cost_le_walk_of_triangle
    (C : SymmetricCost D V)
    (htri : ∀ x y z, C.cost x z ≤ C.cost x y + C.cost y z)
    {x y : V} (p : Walk V x y) :
    C.cost x y ≤ p.weight C := by
  induction p with
  | nil a => simp [Walk.weight, C.cost_self]
  | @step a b z h tail ih =>
      have ht := htri a b z
      change C.cost a z ≤ C.cost a b + tail.weight C
      omega

/-- As expected, shortening an already metric cost matrix
does not change any existing direct distance. -/
theorem shortest_eq_cost_of_triangle
    (C : SymmetricCost D V)
    (htri : ∀ x y z, C.cost x z ≤ C.cost x y + C.cost y z)
    (x y : V) :
    C.shortest x y = C.cost x y :=
  (C.shortest_eq_cost_iff_no_shortcut x y).2
    (fun p => C.cost_le_walk_of_triangle htri p)

/-- Regard an actual bounded metric as a symmetric cost matrix. -/
def ofBoundedMetric (M : BoundedNatMetric D V) :
    SymmetricCost D V where
  cost := M.dist
  cost_self := M.dist_self
  cost_pos := by
    intro x y hxy
    exact M.toNatMetric.dist_pos hxy
  cost_symm := M.dist_symm
  cost_le := M.dist_le

/-- Canonical shortest-path completion fixes every already
metric space, so it acts as a genuine completion operator. -/
theorem shortest_ofBoundedMetric (M : BoundedNatMetric D V)
    (x y : V) :
    (ofBoundedMetric M).shortest x y = M.dist x y :=
  (ofBoundedMetric M).shortest_eq_cost_of_triangle
    M.dist_triangle x y

end SymmetricCost
end IntegerMetric
end AllThoseEPPA
