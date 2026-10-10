import AllThoseEPPA.TreeLikeTwoPathCycle
import AllThoseEPPA.TreeLikeComponentCut

/-!
# Cross-edge locality for paths through different outside components

Suppose p and q are paths with the same endpoints u and v, and
their interior vertices are respectively confined to different
components C and D of the graph outside a separator S containing
u and v.

There can be no cross-component edge. An edge involving an endpoint
of either path must already be an edge of that path if the path is
chordless. Consequently every edge joining the two path supports
belongs to p or q, exactly the cross-edge condition required by
`chordless_cycle_of_two_paths`.

The remaining chordal work is to construct paths with this support
condition and prove disjointness of their *interior* supports,
then convert the resulting chordless Mathlib graph cycle to
`Structure.BadCycleSequence`.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- The cross-edge condition in `chordless_cycle_of_two_paths`
is automatic for chordless paths whose non-endpoint vertices
are supported in two distinct components outside a separator. -/
theorem cross_edges_of_distinct_component_supports
    (G : SimpleGraph V) (S : Set V)
    (C D : (G.induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D)
    {u v : V}
    (p q : G.Walk u v)
    (hp : p.IsChordless)
    (hq : q.IsChordless)
    (hP : ∀ x ∈ p.support,
      x = u ∨ x = v ∨ x ∈ outsideComponent G S C)
    (hQ : ∀ x ∈ q.support,
      x = u ∨ x = v ∨ x ∈ outsideComponent G S D) :
    ∀ a b : V,
      a ∈ p.support → b ∈ q.reverse.support → G.Adj a b →
        s(a,b) ∈ p.edges ∨ s(a,b) ∈ q.reverse.edges := by
  intro a b ha hb hab
  have hbQ : b ∈ q.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hb
  have hQrev : q.reverse.IsChordless := chordless_reverse G q hq
  have hPedge :=
    SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mp hp
  have hQedge :=
    SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mp hQrev
  rcases hP a ha with haU | haV | haC
  · right
    have haQ : a ∈ q.reverse.support := by
      rw [haU]
      exact q.reverse.end_mem_support
    exact hQedge haQ hb hab
  · right
    have haQ : a ∈ q.reverse.support := by
      rw [haV]
      exact q.reverse.start_mem_support
    exact hQedge haQ hb hab
  · rcases hQ b hbQ with hbU | hbV | hbD
    · left
      have hbP : b ∈ p.support := by
        rw [hbU]
        exact p.start_mem_support
      exact hPedge ha hbP hab
    · left
      have hbP : b ∈ p.support := by
        rw [hbV]
        exact p.end_mem_support
      exact hPedge ha hbP hab
    · exact False.elim
        ((outsideComponents_not_adj G S C D hCD a b haC hbD) hab)

end TreeLike
end AllThoseEPPA
