import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import AllThoseEPPA.TreeLikeGraphInterface

/-!
# Cuts along components outside a separator

The graph-theoretic part of Lemma `lem:cuts` repeatedly removes a
clique separator and considers a connected component of the remaining
induced graph. This file gives the underlying decomposition of a
simple graph. It does **not** assume chordality or clique-ness of the
separator: these will be used separately to find a *suitable*
separator and to ensure that its closure remains a separator.

For an arbitrary `S : Set V` and a connected component `C` of
`G.induce Sᶜ`, write `O` for its image in `V`. Then the pair
`S ∪ O` and `Oᶜ` covers all vertices, intersects exactly at `S`,
and has no edges between its exclusive sides. It is a *proper*
cut as soon as there is a vertex outside `S ∪ O`.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- Vertex set of a connected component of the graph induced outside
a candidate separator, viewed in the original vertex type. -/
def outsideComponent (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) : Set V :=
  Subtype.val '' C.supp

theorem outsideComponent_subset_compl
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) :
    outsideComponent G S C ⊆ Sᶜ := by
  rintro x ⟨a, ha, rfl⟩
  exact a.2

/-- Components of `G.induce Sᶜ` are closed under any adjacency that
does not enter `S`. This is the fundamental no-cross-edge fact. -/
theorem outsideComponent_adj
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent)
    {x y : V}
    (hx : x ∈ outsideComponent G S C)
    (hy : y ∈ Sᶜ) (hxy : G.Adj x y) :
    y ∈ outsideComponent G S C := by
  obtain ⟨a, ha, hax⟩ := hx
  subst x
  let b : {z : V // z ∈ Sᶜ} := ⟨y, hy⟩
  have hab : (G.induce Sᶜ).Adj a b := hxy
  exact ⟨b, C.mem_supp_of_adj_mem_supp ha hab, rfl⟩

/-- The first side consists of the separator and one component. -/
def componentCutLeft (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) : Set V :=
  S ∪ outsideComponent G S C

/-- The other side is the complement of the chosen component; it
already contains the separator. -/
def componentCutRight (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) : Set V :=
  (outsideComponent G S C)ᶜ

theorem componentCut_cover
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) :
    componentCutLeft G S C ∪ componentCutRight G S C = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ outsideComponent G S C
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

theorem componentCut_inter
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) :
    componentCutLeft G S C ∩ componentCutRight G S C = S := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨hx, hy⟩
    rcases hx with hxS | hxC
    · exact hxS
    · exact (hy hxC).elim
  · intro hxS
    refine ⟨Or.inl hxS, ?_⟩
    intro hxC
    exact (outsideComponent_subset_compl G S C hxC) hxS

/-- There is no graph edge between the two exclusive sides of a
component cut. No chordality or finiteness is needed. -/
theorem componentCut_no_cross
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (x : V) (hx : x ∈ componentCutLeft G S C)
    (hx' : x ∉ componentCutRight G S C)
    (y : V) (hy : y ∈ componentCutRight G S C)
    (hy' : y ∉ componentCutLeft G S C) :
    ¬ G.Adj x y := by
  intro hxy
  have hxC : x ∈ outsideComponent G S C := by
    by_contra h
    exact hx' h
  have hyCompl : y ∈ Sᶜ := by
    intro hyS
    exact hy' (Or.inl hyS)
  have hyC : y ∈ outsideComponent G S C :=
    outsideComponent_adj G S C hxC hyCompl hxy
  exact hy hyC

/-- The complement of a connected component is always a proper
subset of the vertex set: components are nonempty. -/
theorem componentCutRight_proper
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent) :
    componentCutRight G S C ≠ Set.univ := by
  obtain ⟨a, ha⟩ := C.nonempty_supp
  intro h
  have hxC : (a : V) ∈ outsideComponent G S C :=
    ⟨a, ha, rfl⟩
  have hxR : (a : V) ∈ componentCutRight G S C := by
    rw [h]
    exact Set.mem_univ _
  exact hxR hxC

/-- The component side is proper if some vertex outside the
separator belongs to another connected component. -/
theorem componentCutLeft_proper
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hOther : ∃ y : V, y ∈ Sᶜ ∧ y ∉ outsideComponent G S C) :
    componentCutLeft G S C ≠ Set.univ := by
  obtain ⟨y, hyS, hyO⟩ := hOther
  intro h
  have hy : y ∈ componentCutLeft G S C := by
    rw [h]
    exact Set.mem_univ _
  rcases hy with hs | ho
  · exact hyS hs
  · exact hyO ho

/-- A second, different connected component supplies the other
side required by the previous properness lemma. -/
theorem otherComponent_gives_vertex
    (G : SimpleGraph V) (S : Set V)
    (C D : (G.induce Sᶜ).ConnectedComponent)
    (hne : D ≠ C) :
    ∃ y : V, y ∈ Sᶜ ∧ y ∉ outsideComponent G S C := by
  obtain ⟨a, ha⟩ := D.nonempty_supp
  refine ⟨a.1, a.2, ?_⟩
  rintro ⟨b, hb, hba⟩
  have heq : a = b := Subtype.ext hba.symm
  subst b
  have hDC : D = C :=
    SimpleGraph.ConnectedComponent.eq_of_common_vertex ha hb
  exact hne hDC

end TreeLike
end AllThoseEPPA
