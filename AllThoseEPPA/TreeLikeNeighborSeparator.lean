import AllThoseEPPA.TreeLikeComponentFree

/-!
# A canonical initial vertex separator for nonadjacent vertices

In the chordal-graph part of `lem:cuts` we will choose an inclusion-
minimal separator between two nonadjacent vertices. This file provides
a separator from which the finite minimization can start: the
neighbourhood of either endpoint.

Deleting the neighbors of u isolates u. Thus, for distinct
nonadjacent u,v, the graph induced outside the neighbors of u
has at least two distinct connected components (containing u and v).

No finite-graph or chordality hypotheses are used here. The missing
chordal theorem must show that an *inclusion-minimal* such separator
is a clique.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- After deleting all neighbors of u, the vertex u has no neighbors
in the remaining induced graph. -/
theorem neighbor_deleted_isolated
    (G : SimpleGraph V) (u : V) :
    (G.induce (G.neighborSet u)ᶜ).neighborSet
      (⟨u, G.irrefl⟩ : (G.neighborSet u)ᶜ) = ∅ := by
  ext w
  change G.Adj u w.1 ↔ False
  constructor
  · intro hw
    exact (w.2 hw).elim
  · intro h
    exact False.elim h

/-- Distinct, nonadjacent vertices lie in distinct connected
components after deleting the neighbors of the first one. -/
theorem different_components_outside_neighborSet
    (G : SimpleGraph V) (u v : V)
    (hne : u ≠ v)
    (hnonadj : ¬ G.Adj u v) :
    (G.induce (G.neighborSet u)ᶜ).connectedComponentMk
      (⟨u, G.irrefl⟩ : (G.neighborSet u)ᶜ) ≠
    (G.induce (G.neighborSet u)ᶜ).connectedComponentMk
      (⟨v, hnonadj⟩ : (G.neighborSet u)ᶜ) := by
  let H := G.induce (G.neighborSet u)ᶜ
  let u₀ : (G.neighborSet u)ᶜ := ⟨u, G.irrefl⟩
  let v₀ : (G.neighborSet u)ᶜ := ⟨v, hnonadj⟩
  have hne₀ : u₀ ≠ v₀ := by
    intro h
    exact hne (congrArg Subtype.val h)
  have hnotReach : ¬ H.Reachable u₀ v₀ :=
    SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
      hne₀ (neighbor_deleted_isolated G u)
  intro hEq
  have hr : H.Reachable u₀ v₀ :=
    (SimpleGraph.ConnectedComponent.eq).mp hEq
  exact hnotReach hr

/-- Every finite (indeed any) noncomplete simple graph has a
vertex set whose deletion leaves at least two components. This
is the existence input for choosing a minimal separator. -/
theorem exists_disconnecting_neighborSet
    (G : SimpleGraph V)
    (hnotComplete : ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v) :
    ∃ (S : Set V)
      (C D : (G.induce Sᶜ).ConnectedComponent), C ≠ D := by
  obtain ⟨u, v, hne, hno⟩ := hnotComplete
  refine ⟨G.neighborSet u, _, _, ?_⟩
  exact different_components_outside_neighborSet G u v hne hno

end TreeLike
end AllThoseEPPA
