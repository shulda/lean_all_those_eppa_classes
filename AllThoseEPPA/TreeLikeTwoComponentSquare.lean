import AllThoseEPPA.TreeLikeSquareObstruction
import AllThoseEPPA.TreeLikeComponentCut

/-!
# Induced squares crossing two different graph components

If x,y lie in a proposed vertex separator and are nonadjacent,
a common neighbor of x and y in each of two distinct components
outside the separator yields an induced square. The components
cannot be adjacent to each other, and their vertices are disjoint
from the separator.

Thus this simplest form of the minimal-separator clique obstruction
is excluded by `lem:sparsen`'s no-induced-cycle alternative.
For the full chordal clique-separator theorem, the paths through
the components may be longer than two edges; the same geometry
will ultimately require a general induced-path concatenation.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- A vertex outside S cannot lie in two distinct connected
components of the graph induced on Sᶜ. -/
theorem outsideComponents_disjoint
    (G : SimpleGraph V) (S : Set V)
    (C D : (G.induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D)
    (x : V)
    (hxC : x ∈ outsideComponent G S C)
    (hxD : x ∈ outsideComponent G S D) : False := by
  obtain ⟨a, ha, hax⟩ := hxC
  obtain ⟨b, hb, hbx⟩ := hxD
  have hab : a = b := Subtype.ext (hax.trans hbx.symm)
  subst b
  have hEq : C = D :=
    SimpleGraph.ConnectedComponent.eq_of_common_vertex ha hb
  exact hCD hEq

/-- Vertices in different outside components cannot be adjacent. -/
theorem outsideComponents_not_adj
    (G : SimpleGraph V) (S : Set V)
    (C D : (G.induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D)
    (x y : V)
    (hx : x ∈ outsideComponent G S C)
    (hy : y ∈ outsideComponent G S D) :
    ¬ G.Adj x y := by
  intro hxy
  have hyOut : y ∈ Sᶜ :=
    outsideComponent_subset_compl G S D hy
  have hyC : y ∈ outsideComponent G S C :=
    outsideComponent_adj G S C hx hyOut hxy
  exact outsideComponents_disjoint G S C D hCD y hyC hy

variable {L : Language}

/-- A pair of nonadjacent separator vertices cannot have a
length-two path through each of two distinct outside components
of a chordal graph. The resulting forbidden induced square is
constructed explicitly in the same `BadCycleSequence` API as
the cycle-sparsening lemma. -/
theorem no_common_neighbors_in_two_components
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ q : Structure.BadCycleSequence B E, False)
    (S : Set V)
    (C D : ((distinguishedGraph B E hloop hsymm).induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D)
    (x y c d : V)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hxy : x ≠ y)
    (hnoXY : ¬ B.Edge E x y)
    (hc : c ∈ outsideComponent
      (distinguishedGraph B E hloop hsymm) S C)
    (hd : d ∈ outsideComponent
      (distinguishedGraph B E hloop hsymm) S D)
    (hxc : B.Edge E x c)
    (hcy : B.Edge E c y)
    (hyd : B.Edge E y d)
    (hdx : B.Edge E d x) : False := by
  let G : SimpleGraph V := distinguishedGraph B E hloop hsymm
  have hcOut : c ∈ Sᶜ :=
    outsideComponent_subset_compl G S C hc
  have hdOut : d ∈ Sᶜ :=
    outsideComponent_subset_compl G S D hd
  have hxcNe : x ≠ c := by
    intro h
    subst c
    exact hcOut hxS
  have hxdNe : x ≠ d := by
    intro h
    subst d
    exact hdOut hxS
  have hcyNe : c ≠ y := by
    intro h
    subst c
    exact hcOut hyS
  have hydNe : y ≠ d := by
    intro h
    subst d
    exact hdOut hyS
  have hcdNe : c ≠ d := by
    intro h
    subst d
    exact outsideComponents_disjoint G S C D hCD c hc hd
  have hcdNo : ¬ B.Edge E c d := by
    have h : ¬ G.Adj c d :=
      outsideComponents_not_adj G S C D hCD c d hc hd
    exact h
  exact no_induced_square_of_no_bad_cycles
    B E hloop hsymm hNo
    x c y d
    hxcNe hxy hxdNe hcyNe hcdNe hydNe
    hxc hcy hyd hdx hnoXY hcdNo

end TreeLike
end AllThoseEPPA
