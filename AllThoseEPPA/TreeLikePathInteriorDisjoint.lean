import AllThoseEPPA.TreeLikeCrossComponentEdges

/-!
# Interior-disjointness for two separator-component paths

Suppose p and q are simple graph paths with the same endpoints u,v,
where both endpoints lie in S and every other vertex of p (respectively q)
lies in a component C (respectively D) of G induced outside S.
If C ≠ D then the two paths are internally disjoint.

This is stated in precisely the `List.Disjoint` orientation needed by
`SimpleGraph.Walk.IsPath.isCycle_append` when forming
`p.append q.reverse`. The proof uses only the support nodup of paths,
disjointness of distinct connected components, and avoidance of S.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- A path cannot return to its initial vertex after the first step. -/
theorem path_start_not_mem_tail
    (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) :
    u ∉ p.support.tail := by
  cases p with
  | nil =>
      simp
  | cons h p =>
      have hn : (u :: p.support).Nodup := by
        simpa only [SimpleGraph.Walk.support_cons] using hp.support_nodup
      exact (List.nodup_cons.mp hn).1

/-- Two paths through distinct outside components have disjoint
interiors, in the orientation required by the two-path cycle lemma. -/
theorem distinct_component_paths_disjoint_interiors
    (G : SimpleGraph V) (S : Set V)
    (C D : (G.induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D)
    {u v : V}
    (huS : u ∈ S) (hvS : v ∈ S)
    (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (hP : ∀ x ∈ p.support,
      x = u ∨ x = v ∨ x ∈ outsideComponent G S C)
    (hQ : ∀ x ∈ q.support,
      x = u ∨ x = v ∨ x ∈ outsideComponent G S D) :
    p.support.tail.Disjoint q.reverse.support.tail := by
  intro x hx hy
  have hxP : x ∈ p.support :=
    List.mem_of_mem_tail hx
  have hxQ : x ∈ q.support := by
    have hy' : x ∈ q.reverse.support :=
      List.mem_of_mem_tail hy
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hy'
  have hnu : u ∉ p.support.tail :=
    path_start_not_mem_tail G p hp
  have hnv : v ∉ q.reverse.support.tail :=
    path_start_not_mem_tail G q.reverse hq.reverse
  rcases hP x hxP with hxu | hxv | hxC
  · exact hnu (hxu ▸ hx)
  · exact hnv (hxv ▸ hy)
  · rcases hQ x hxQ with hxu | hxv | hxD
    · have hxOut : x ∈ Sᶜ :=
        outsideComponent_subset_compl G S C hxC
      exact hxOut (hxu ▸ huS)
    · have hxOut : x ∈ Sᶜ :=
        outsideComponent_subset_compl G S C hxC
      exact hxOut (hxv ▸ hvS)
    · exact outsideComponents_disjoint G S C D hCD x hxC hxD

/-- For component-supported chordless paths, the two-path assembly
gives a chordless cycle without any additional cross-edge or
disjointness hypotheses. -/
theorem chordless_cycle_of_distinct_component_paths
    (G : SimpleGraph V) (S : Set V)
    (C D : (G.induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D)
    {u v : V}
    (huS : u ∈ S) (hvS : v ∈ S)
    (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (hChordP : p.IsChordless) (hChordQ : q.IsChordless)
    (hLength : 1 < p.length)
    (hP : ∀ x ∈ p.support,
      x = u ∨ x = v ∨ x ∈ outsideComponent G S C)
    (hQ : ∀ x ∈ q.support,
      x = u ∨ x = v ∨ x ∈ outsideComponent G S D) :
    (p.append q.reverse).IsCycle ∧
      (p.append q.reverse).IsChordless := by
  exact chordless_cycle_of_two_paths G p q hp hq
    hChordP hChordQ
    (distinct_component_paths_disjoint_interiors
      G S C D hCD huS hvS p q hp hq hP hQ)
    hLength
    (cross_edges_of_distinct_component_supports
      G S C D hCD p q hChordP hChordQ hP hQ)

end TreeLike
end AllThoseEPPA
