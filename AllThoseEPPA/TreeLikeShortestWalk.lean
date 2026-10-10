import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-!
# Shortest walks have no repeated vertices or long chords

A proof of the chordal clique-separator theorem ultimately needs
two *induced* paths connecting two nonadjacent separator vertices
through different components. We begin with the generic shortest-
walk argument, independently of separators.

For any reachable vertices, choose a walk of minimum length by
`Nat.find`. Such a walk is a path. If two of its vertices at
indices i < j with i+1 < j were adjacent, using that chord as a
shortcut would yield a strictly shorter walk, contradiction.

This is the key local property needed to obtain chordless paths
through connected components.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- Every reachable pair of vertices has a shortest walk.
No finiteness hypothesis on the graph or carrier is needed. -/
theorem exists_shortest_walk
    (G : SimpleGraph V) {u v : V}
    (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, ∀ q : G.Walk u v, p.length ≤ q.length := by
  classical
  let P : ℕ → Prop :=
    fun n => ∃ p : G.Walk u v, p.length = n
  have hex : ∃ n, P n := by
    obtain ⟨p⟩ := hr
    exact ⟨p.length, p, rfl⟩
  obtain ⟨p, hp⟩ := Nat.find_spec hex
  refine ⟨p, ?_⟩
  intro q
  have hmin : Nat.find hex ≤ q.length :=
    Nat.find_min' hex ⟨q, rfl⟩
  rw [← hp] at hmin
  exact hmin

/-- A walk of shortest length is automatically a path,
since removing any repetitions cannot increase its length. -/
theorem shortest_walk_isPath
    (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v)
    (hmin : ∀ q : G.Walk u v, p.length ≤ q.length) :
    p.IsPath := by
  classical
  have hlen : p.length ≤ p.bypass.length := by
    exact hmin (p.toPath : G.Walk u v)
  have heq : p.bypass = p :=
    (SimpleGraph.Walk.length_le_bypass_length_iff p).mp hlen
  exact (show p.bypass = p ↔ p.IsPath from
    SimpleGraph.Walk.bypass_eq_self_iff_isPath).mp heq

/-- A shortest walk has no chord that skips at least one edge.
The candidate shortcut is the concatenation of the prefix to
index i, the new edge from i to j, and the suffix from index j. -/
theorem shortest_walk_no_long_chord
    (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v)
    (hmin : ∀ q : G.Walk u v, p.length ≤ q.length)
    (i j : ℕ)
    (hi : i ≤ p.length)
    (hj : j ≤ p.length)
    (hij : i + 1 < j) :
    ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro hChord
  let q : G.Walk u v :=
    (p.take i).append (hChord.toWalk.append (p.drop j))
  have hq : q.length = i + 1 + (p.length - j) := by
    dsimp [q]
    simp only [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil,
      SimpleGraph.Walk.take_length,
      SimpleGraph.Walk.drop_length,
      Nat.min_eq_left hi]
    omega
  have hge : p.length ≤ q.length := hmin q
  omega

end TreeLike
end AllThoseEPPA
