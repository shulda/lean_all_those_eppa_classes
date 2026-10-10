import AllThoseEPPA.TreeLikeShortestWalk
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord

/-!
# A shortest graph walk is an induced (chordless) path

This closes the first generic path-theoretic obligation in the
chordal clique-separator argument. The preceding module proves
that a shortest walk cannot have an edge between vertices
separated by two or more steps. Converting support membership
into indexed vertices and analyzing their index distances now
shows that every edge between vertices of a shortest walk is
an edge of the walk itself.

Consequently, connectedness always supplies a chordless path.
This result does not assume graph finiteness or chordality.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- A shortest walk is chordless. -/
theorem shortest_walk_isChordless
    (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v)
    (hmin : ∀ q : G.Walk u v, p.length ≤ q.length) :
    p.IsChordless := by
  classical
  apply SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mpr
  intro a b ha hb hab
  obtain ⟨i, hi, hiLen⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_getVert).mp ha
  obtain ⟨j, hj, hjLen⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_getVert).mp hb
  have hine : i ≠ j := by
    intro hEq
    have habEq : a = b := by
      calc
        a = p.getVert i := hi.symm
        _ = p.getVert j := by rw [hEq]
        _ = b := hj
    exact hab.ne habEq
  have hijNo : ¬ i + 1 < j := by
    intro hlong
    have hshortcut :=
      shortest_walk_no_long_chord G p hmin i j hiLen hjLen hlong
    exact hshortcut (by simpa [hi, hj] using hab)
  have hjiNo : ¬ j + 1 < i := by
    intro hlong
    have hshortcut :=
      shortest_walk_no_long_chord G p hmin j i hjLen hiLen hlong
    exact hshortcut (by simpa [hi, hj] using hab.symm)
  have hAdjIndex : j = i + 1 ∨ i = j + 1 := by omega
  rcases hAdjIndex with h | h
  · apply (SimpleGraph.Walk.mk_mem_edges_iff_exists p).2
    refine ⟨i, by omega, ?_⟩
    rw [← h, hi, hj]
  · apply (SimpleGraph.Walk.mk_mem_edges_iff_exists p).2
    refine ⟨j, by omega, ?_⟩
    calc
      s(p.getVert j, p.getVert (j + 1)) = s(b, a) := by
        rw [← h, hj, hi]
      _ = s(a, b) := Sym2.eq_swap

/-- Every reachable pair of graph vertices can be joined by an
induced (chordless) path. The path is represented as a walk
equipped with its `IsPath` and `IsChordless` certificates. -/
theorem exists_chordless_path
    (G : SimpleGraph V) {u v : V}
    (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.IsChordless := by
  obtain ⟨p, hmin⟩ := exists_shortest_walk G hr
  exact ⟨p, shortest_walk_isPath G p hmin,
    shortest_walk_isChordless G p hmin⟩

end TreeLike
end AllThoseEPPA
