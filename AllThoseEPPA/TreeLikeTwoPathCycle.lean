import AllThoseEPPA.TreeLikeChordlessReverse
import AllThoseEPPA.TreeLikeChordlessAppend
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Two induced paths produce an induced graph cycle

Given two internally disjoint induced paths from the same u to v,
the concatenation of the first with the reverse of the second is a
cycle. A cross-edge locality hypothesis ensures that this cycle
has no chords. This is the graph-theoretic assembly step required
for the clique-separator argument in Lemma `lem:cuts`.

The separate remaining task is to obtain the cross-edge condition
from paths through two distinct outside components (and to convert
this graph cycle into the existing BadCycleSequence API).
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- Two internally disjoint paths between u and v give a cycle.
The length hypothesis ensures the cycle has at least three edges. -/
theorem cycle_of_disjoint_paths
    (G : SimpleGraph V) {u v : V}
    (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (hDisj : p.support.tail.Disjoint q.reverse.support.tail)
    (hLength : 1 < p.length) :
    (p.append q.reverse).IsCycle := by
  exact hp.isCycle_append hq.reverse hDisj (Or.inl hLength)

/-- If the two paths have no additional cross-support edges,
their union gives an induced, i.e. chordless, graph cycle. -/
theorem chordless_cycle_of_two_paths
    (G : SimpleGraph V) {u v : V}
    (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (hChordP : p.IsChordless) (hChordQ : q.IsChordless)
    (hDisj : p.support.tail.Disjoint q.reverse.support.tail)
    (hLength : 1 < p.length)
    (hCross : ∀ a b : V,
      a ∈ p.support → b ∈ q.reverse.support → G.Adj a b →
        s(a,b) ∈ p.edges ∨ s(a,b) ∈ q.reverse.edges) :
    (p.append q.reverse).IsCycle ∧
      (p.append q.reverse).IsChordless := by
  refine ⟨cycle_of_disjoint_paths G p q hp hq hDisj hLength, ?_⟩
  exact chordless_append_of_cross_edges G p q.reverse
    hChordP (chordless_reverse G q hChordQ) hCross

end TreeLike
end AllThoseEPPA
