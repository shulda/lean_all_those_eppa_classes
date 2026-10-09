import Mathlib.Data.Set.Card
import AllThoseEPPA.TreeLikeNeighborSeparator

/-!
# Existence of inclusion-minimal separators in finite graphs

The chordal-cut lemma needs a *minimal* vertex separator, not just
any set whose deletion disconnects the graph. This file supplies
the finite minimization argument, independently of chordality.

A separator S of u and v is a set avoiding u,v such that these
vertices lie in distinct connected components of G induced on Sᶜ.
For distinct nonadjacent u,v, the neighborhood of u is such a
separator. When the vertex type is finite, choose one of smallest
cardinality using `Nat.find`; it is automatically inclusion-minimal.

The remaining genuinely chordal theorem must prove that every
inclusion-minimal separator is a clique.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- A vertex separator for u and v: deleting it keeps u,v,
but separates their connected components. -/
def SeparatesVertices (G : SimpleGraph V)
    (u v : V) (S : Set V) : Prop :=
  ∃ (hu : u ∈ Sᶜ) (hv : v ∈ Sᶜ),
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ ≠
      (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩

/-- The neighborhood of u separates u from any distinct
nonadjacent vertex v. -/
theorem neighborSet_separates
    (G : SimpleGraph V) (u v : V)
    (hne : u ≠ v)
    (hnonadj : ¬ G.Adj u v) :
    SeparatesVertices G u v (G.neighborSet u) :=
  ⟨G.irrefl, hnonadj,
    different_components_outside_neighborSet G u v hne hnonadj⟩

/-- Among all sets separating distinct nonadjacent vertices,
one has minimal cardinality. This uses only finiteness of V
and well-ordering of the natural numbers. -/
theorem exists_cardinality_minimal_separator
    [Finite V] (G : SimpleGraph V) (u v : V)
    (hne : u ≠ v)
    (hnonadj : ¬ G.Adj u v) :
    ∃ S : Set V, SeparatesVertices G u v S ∧
      ∀ T : Set V, SeparatesVertices G u v T → S.ncard ≤ T.ncard := by
  classical
  let P : ℕ → Prop :=
    fun k => ∃ S : Set V, SeparatesVertices G u v S ∧ S.ncard = k
  have hex : ∃ k, P k := by
    refine ⟨(G.neighborSet u).ncard, G.neighborSet u, ?_, rfl⟩
    exact neighborSet_separates G u v hne hnonadj
  obtain ⟨S, hS, hsize⟩ := Nat.find_spec hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  have hbound : Nat.find hex ≤ T.ncard :=
    Nat.find_min' hex ⟨T, hT, rfl⟩
  simpa [hsize] using hbound

/-- In particular, a separator of smallest cardinality is
inclusion-minimal. This is the exact starting point of the
clique-separator proof for finite chordal graphs. -/
theorem exists_inclusion_minimal_separator
    [Finite V] (G : SimpleGraph V) (u v : V)
    (hne : u ≠ v)
    (hnonadj : ¬ G.Adj u v) :
    ∃ S : Set V, SeparatesVertices G u v S ∧
      ∀ T : Set V, T ⊂ S → ¬ SeparatesVertices G u v T := by
  obtain ⟨S, hS, hmin⟩ :=
    exists_cardinality_minimal_separator G u v hne hnonadj
  refine ⟨S, hS, ?_⟩
  intro T hproper hsep
  have hlt : T.ncard < S.ncard :=
    Set.ncard_lt_ncard hproper (Set.toFinite S)
  exact (not_lt_of_ge (hmin T hsep)) hlt

end TreeLike
end AllThoseEPPA
