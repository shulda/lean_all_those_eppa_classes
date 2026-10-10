import AllThoseEPPA.TreeLikePathInteriorDisjoint
import AllThoseEPPA.TreeLikeComponentNeighborhoodPath
import AllThoseEPPA.TreeLikeNonadjacentPathLength
import AllThoseEPPA.TreeLikeCycleTranslation
import AllThoseEPPA.TreeLikeMinimalClosed
import AllThoseEPPA.TreeLikeIrreducibleSeparator

/-!
# Minimal vertex separators in chordal graphs are cliques

This is the graph-theoretic heart of the paper's Lemma `lem:cuts`.

For a finite graph without induced cycles of length at least four,
an inclusion-minimal separator S between two vertices u,v is a clique.
Indeed, suppose distinct x,y ∈ S are nonadjacent. Minimality forces
x and y to have neighbors in each of the u- and v-components of
G induced on Sᶜ. Shortest induced paths x-y through those different
components exist, have internally disjoint supports and no cross
edges except walk edges. They therefore combine to a chordless
graph cycle of length at least four, contradiction.

The structural corollary connects the graph statement to the exact
`BadCycleSequence` predicate of `lem:sparsen`, then uses the already
verified automatic function closure of minimal separators to
conclude that such a separator is an irreducible substructure.

The later construction of a tree amalgamation of copies of A
remains a separate obligation.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- Chordality expressed by excluding Mathlib's induced cycles
of length at least four. This is later shown equivalent to the
relevant BadCycleSequence exclusion for the distinguished E graph. -/
def NoLongChordlessCycles (G : SimpleGraph V) : Prop :=
  ∀ ⦃u : V⦄ (p : G.Walk u u),
    p.IsCycle → p.IsChordless → p.length < 4

/-- **Chordal separator theorem (pure graph form).**
Every inclusion-minimal u-v vertex separator of a graph without
long induced cycles is a clique. -/
theorem minimal_separator_graph_isClique
    (G : SimpleGraph V)
    (hNo : NoLongChordlessCycles G)
    (u v : V) (S : Set V)
    (hu : u ∈ Sᶜ) (hv : v ∈ Sᶜ)
    (hsep :
      (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ ≠
        (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩)
    (hmin : ∀ T : Set V, T ⊂ S →
      ¬ SeparatesVertices G u v T) :
    G.IsClique S := by
  change S.Pairwise G.Adj
  intro x hx y hy hxy
  by_contra hNonEdge
  let C : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩
  let D : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩
  have hCD : C ≠ D := hsep
  obtain ⟨⟨c1, hc1, hxc1⟩, ⟨d1, hd1, hxd1⟩⟩ :=
    minimal_separator_two_sided_neighbors
      G u v S hu hv hsep hmin x hx
  obtain ⟨⟨c2, hc2, hyc2⟩, ⟨d2, hd2, hyd2⟩⟩ :=
    minimal_separator_two_sided_neighbors
      G u v S hu hv hsep hmin y hy
  obtain ⟨p, hp, hChordP, hP⟩ :=
    exists_chordless_path_through_component G S C x y
      ⟨c1, hc1, hxc1⟩ ⟨c2, hc2, hyc2.symm⟩
  obtain ⟨q, hq, hChordQ, hQ⟩ :=
    exists_chordless_path_through_component G S D x y
      ⟨d1, hd1, hxd1⟩ ⟨d2, hd2, hyd2.symm⟩
  have hLenP : 1 < p.length :=
    nonadjacent_walk_length_gt_one G hxy hNonEdge p
  have hLenQ : 1 < q.length :=
    nonadjacent_walk_length_gt_one G hxy hNonEdge q
  obtain ⟨hCycle, hChord⟩ :=
    chordless_cycle_of_distinct_component_paths
      G S C D hCD hx hy p q hp hq hChordP hChordQ
      hLenP hP hQ
  have hLong : 4 ≤ (p.append q.reverse).length := by
    rw [SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse]
    omega
  have hShort := hNo (p.append q.reverse) hCycle hChord
  omega

universe w
variable {L : Language.{w}}

/-- The no-bad-cycle hypothesis from `lem:sparsen` forces the
distinguished E-graph to be chordal in the exact graph sense. -/
theorem distinguishedGraph_noLongChordlessCycles
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False) :
    NoLongChordlessCycles (distinguishedGraph B E hloop hsymm) := by
  intro u p hcyc hchord
  exact no_chordless_long_graph_cycle
    B E hloop hsymm hNo p hcyc hchord

/-- **Chordal separator theorem in the EPPA API.**
An inclusion-minimal separator of a structure with no forbidden
induced E-cycles is an E-clique. -/
theorem minimal_separator_edgeClique
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False)
    (u v : V) (S : Set V)
    (hu : u ∈ Sᶜ) (hv : v ∈ Sᶜ)
    (hsep :
      ((distinguishedGraph B E hloop hsymm).induce Sᶜ).connectedComponentMk
        ⟨u, hu⟩ ≠
      ((distinguishedGraph B E hloop hsymm).induce Sᶜ).connectedComponentMk
        ⟨v, hv⟩)
    (hmin : ∀ T : Set V, T ⊂ S →
      ¬ SeparatesVertices
        (distinguishedGraph B E hloop hsymm) u v T) :
    EdgeClique B E S := by
  apply (edgeClique_iff_graphClique B E hloop hsymm S).mpr
  exact minimal_separator_graph_isClique
    (distinguishedGraph B E hloop hsymm)
    (distinguishedGraph_noLongChordlessCycles
      B E hloop hsymm hNo)
    u v S hu hv hsep hmin

/-- **Chordal irreducible-cut theorem.**
For unary-function structures, a minimal separator in the
distinguished chordal E-reduct is both closed and irreducible
if all irreducible substructures are E-cliques. -/
theorem minimal_separator_isIrreducible
    [L.HasUnaryFunctions]
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False)
    (u v : V) (S : Set V)
    (hu : u ∈ Sᶜ) (hv : v ∈ Sᶜ)
    (hsep :
      ((distinguishedGraph B E hloop hsymm).induce Sᶜ).connectedComponentMk
        ⟨u, hu⟩ ≠
      ((distinguishedGraph B E hloop hsymm).induce Sᶜ).connectedComponentMk
        ⟨v, hv⟩)
    (hmin : ∀ T : Set V, T ⊂ S →
      ¬ SeparatesVertices
        (distinguishedGraph B E hloop hsymm) u v T) :
    (B.induce S
      (minimal_separator_isClosed B E hIrred hloop hsymm
        u v S hu hv hsep hmin)).IsIrreducible := by
  exact closed_edgeClique_isIrreducible B E S
    (minimal_separator_isClosed B E hIrred hloop hsymm
      u v S hu hv hsep hmin)
    (minimal_separator_edgeClique B E hloop hsymm hNo
      u v S hu hv hsep hmin)

end TreeLike
end AllThoseEPPA
