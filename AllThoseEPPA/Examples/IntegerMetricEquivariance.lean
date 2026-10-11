import AllThoseEPPA.Examples.IntegerMetricShortestPaths

/-!
# Equivariance of canonical shortest-path metric completion

The canonical completion must preserve automorphisms *without*
choosing arbitrary paths or a preferred vertex order. We prove the
stronger assertion that every cost-preserving permutation of the
original symmetric cost matrix is automatically an isometry of
the completed metric.

The key is transport of finite walks by arbitrary equivalences.
Walk weight is unchanged whenever the vertex equivalence preserves
the costs of the individual steps. Applying this in both directions
shows equality of minimum walk lengths.

This theorem is the automorphism-equivariant component needed by
the later automorphism-preserving locally finite metric completion
interface (and ultimately coherent EPPA).
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u v

namespace Walk

/-- Transport a walk through a vertex equivalence. -/
def map {V : Type u} {W : Type v} (e : V ≃ W)
    {x y : V} (p : Walk V x y) :
    Walk W (e x) (e y) :=
  match p with
  | .nil a => .nil (e a)
  | .step (x := a) (y := b) h tail =>
      .step (fun heq => h (e.injective heq)) (map e tail)

/-- Equivalences which preserve each direct cost also preserve
the total weight of any transported finite walk. -/
theorem weight_map {D : ℕ} {V : Type u} {W : Type v}
    (e : V ≃ W)
    (C : SymmetricCost D V) (B : SymmetricCost D W)
    (hCost : ∀ x y, B.cost (e x) (e y) = C.cost x y)
    {x y : V} (p : Walk V x y) :
    (p.map e).weight B = p.weight C := by
  induction p with
  | nil a => rfl
  | @step a b z h tail ih =>
      change B.cost (e a) (e b) + (tail.map e).weight B =
        C.cost a b + tail.weight C
      rw [hCost a b, ih]

end Walk

namespace SymmetricCost

variable {D : ℕ} {V : Type u}

/-- Every permutation preserving the underlying cost matrix
preserves the shortest path distance exactly. -/
theorem shortest_equivariant
    (C : SymmetricCost D V)
    (g : Equiv.Perm V)
    (hCost : ∀ x y, C.cost (g x) (g y) = C.cost x y)
    (x y : V) :
    C.shortest (g x) (g y) = C.shortest x y := by
  have hCostInv :
      ∀ x y, C.cost (g.symm x) (g.symm y) = C.cost x y := by
    intro a b
    have h := hCost (g.symm a) (g.symm b)
    simpa only [Equiv.apply_symm_apply] using h.symm
  have hForward :
      C.shortest (g x) (g y) ≤ C.shortest x y := by
    obtain ⟨p, hp⟩ := C.exists_shortest_walk x y
    have h := C.shortest_le_walk (p.map g)
    rw [Walk.weight_map g C C hCost p, hp] at h
    exact h
  have hBackward :
      C.shortest x y ≤ C.shortest (g x) (g y) := by
    obtain ⟨p, hp⟩ := C.exists_shortest_walk (g x) (g y)
    have h := C.shortest_le_walk (p.map g.symm)
    rw [Walk.weight_map g.symm C C hCostInv p, hp] at h
    simpa only [Equiv.symm_apply_apply] using h
  exact Nat.le_antisymm hForward hBackward

/-- The same statement in terms of the actual bounded integer
metric produced by shortest-path completion. -/
theorem completedMetric_equivariant
    (C : SymmetricCost D V)
    (g : Equiv.Perm V)
    (hCost : ∀ x y, C.cost (g x) (g y) = C.cost x y)
    (x y : V) :
    C.completedMetric.dist (g x) (g y) =
      C.completedMetric.dist x y :=
  C.shortest_equivariant g hCost x y

end SymmetricCost
end IntegerMetric
end AllThoseEPPA
