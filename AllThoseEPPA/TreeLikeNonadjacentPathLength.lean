import AllThoseEPPA.TreeLikeTwoPathCycle
import Lean.Elab.Tactic.Omega

/-!
# Every walk joining two distinct nonadjacent vertices has length at least two

For the chordal separator argument, two induced paths joining a
nonadjacent pair x,y must each use at least two edges. This ensures
that the closed walk formed from the two internally disjoint paths
has length at least four, as required by the EPPA `BadCycleSequence`
notion of a forbidden induced cycle.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- A walk between two distinct nonadjacent vertices has at least
two edges. No simplicity or chordlessness assumption on the walk
is needed. -/
theorem nonadjacent_walk_length_gt_one
    (G : SimpleGraph V) {u v : V}
    (hne : u ≠ v) (hnonadj : ¬ G.Adj u v)
    (p : G.Walk u v) :
    1 < p.length := by
  by_contra hle'
  have hle : p.length ≤ 1 := by omega
  by_cases hzero : p.length = 0
  · have heq : u = v := by
      have h := p.getVert_of_length_le (i := 0) (by omega)
      simpa only [SimpleGraph.Walk.getVert_zero] using h
    exact hne heq
  · have hone : p.length = 1 := by omega
    have hadj : G.Adj (p.getVert 0) (p.getVert 1) :=
      p.adj_getVert_succ (i := 0) (by omega)
    have hlast : p.getVert 1 = v := by
      simpa only [hone] using p.getVert_length
    have hUV : G.Adj u v := by
      simpa only [SimpleGraph.Walk.getVert_zero, hlast] using hadj
    exact hnonadj hUV

end TreeLike
end AllThoseEPPA
