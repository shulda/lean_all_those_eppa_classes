import AllThoseEPPA.TreeLikeMinimalSeparator
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Reachability cannot leave an adjacency-closed vertex set

This graph-theoretic lemma is the next basic tool for proving that an
inclusion-minimal separator is essential at each of its vertices.

If a vertex set T contains all neighbors (in an induced graph) of
every vertex it contains, no walk starting in T can leave T. Thus
two vertices on opposite sides of T cannot be connected by a walk.

We will apply this to a connected component of G induced outside
a separator S, after reinserting a candidate redundant separator
vertex. If that vertex has no neighbor in the component, the
component remains adjacency-closed and still separates u and v,
contradicting minimality.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- Closure under single graph edges implies closure under arbitrary
finite walks, hence under reachability. -/
theorem mem_of_reachable_of_adj_closed
    (G : SimpleGraph V) (T : Set V)
    (hclosed : ∀ {x y : V}, x ∈ T → G.Adj x y → y ∈ T)
    {u v : V}
    (hu : u ∈ T)
    (hr : G.Reachable u v) :
    v ∈ T := by
  obtain ⟨p⟩ := hr
  have hwalk : ∀ {x y : V} (q : G.Walk x y),
      x ∈ T → y ∈ T := by
    intro x y q
    induction q with
    | nil =>
        intro hx
        exact hx
    | cons h q ih =>
        intro hx
        exact ih (hclosed hx h)
  exact hwalk p hu

/-- Consequently, an adjacency-closed set separates every vertex
it contains from every vertex in its complement. -/
theorem not_reachable_of_adj_closed
    (G : SimpleGraph V) (T : Set V)
    (hclosed : ∀ {x y : V}, x ∈ T → G.Adj x y → y ∈ T)
    {u v : V}
    (hu : u ∈ T) (hv : v ∉ T) :
    ¬ G.Reachable u v := by
  intro hr
  exact hv (mem_of_reachable_of_adj_closed G T hclosed hu hr)

end TreeLike
end AllThoseEPPA
