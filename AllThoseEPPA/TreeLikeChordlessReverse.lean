import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Reverse and concatenation of chordless walks

Reversing a chordless graph walk preserves chordlessness.
This is a basic tool for joining paths found in different components
of the complement of a vertex separator, in the ongoing formalization
of the chordal-cut lemma.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- Reversing a chordless graph walk yields another chordless walk. -/
theorem chordless_reverse
    (G : SimpleGraph V) {a b : V}
    (p : G.Walk a b) (hp : p.IsChordless) :
    p.reverse.IsChordless := by
  apply SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mpr
  intro x y hx hy hxy
  have hx' : x ∈ p.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hx
  have hy' : y ∈ p.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hy
  have hed : s(x,y) ∈ p.edges :=
    (SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mp hp)
      hx' hy' hxy
  simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hed

end TreeLike
end AllThoseEPPA
