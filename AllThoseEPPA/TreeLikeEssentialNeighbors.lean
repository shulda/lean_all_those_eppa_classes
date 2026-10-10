import AllThoseEPPA.TreeLikeWalkClosure

/-!
# Essential vertices of a minimal graph separator

For a separator S of distinct vertices u,v, inclusion-minimality
forces every s ∈ S to have a neighbor in *each* of the two components
containing u and v in the induced graph outside S.

We prove this by contradiction. If s has no neighbor in the
u-component C, reinsert s by deleting only S \ {s}. The image of C
in the larger induced graph remains adjacency-closed, since:
* neighbors outside S already lie in C;
* an edge from C to the newly reinserted s contradicts the absence
  of an s-neighbor in C.

Thus no walk can reach v from u after reinserting s, so S \ {s}
still separates them, contradicting inclusion minimality.

This supplies the missing two-sided-neighbor hypothesis of
`two_sided_separator_isClosed` and is independent of chordality.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- The definition of vertex separation is symmetric in the two
vertices. -/
theorem separatesVertices_comm (G : SimpleGraph V)
    (u v : V) (S : Set V) :
    SeparatesVertices G u v S ↔ SeparatesVertices G v u S := by
  constructor
  · rintro ⟨hu, hv, hne⟩
    exact ⟨hv, hu, hne.symm⟩
  · rintro ⟨hv, hu, hne⟩
    exact ⟨hu, hv, hne.symm⟩

/-- Every vertex of an inclusion-minimal u-v separator has a
neighbor in the component of u outside the separator. -/
theorem minimal_separator_neighbor_endpoint
    (G : SimpleGraph V) (u v : V) (S : Set V)
    (hu : u ∈ Sᶜ) (hv : v ∈ Sᶜ)
    (hsep :
      (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ ≠
        (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩)
    (hmin : ∀ T : Set V, T ⊂ S →
      ¬ SeparatesVertices G u v T)
    (s : V) (hs : s ∈ S) :
    ∃ c : V, c ∈ outsideComponent G S
      ((G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩) ∧
      G.Adj s c := by
  classical
  let C : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩
  by_contra hno
  let S' : Set V := S \ {s}
  have hsubset : S' ⊆ S := by
    intro x hx
    exact hx.1
  have hproper : S' ⊂ S := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hsubset, ?_⟩
    intro heq
    have hs' : s ∈ S' := by rw [heq]; exact hs
    exact hs'.2 (by simp)
  have hu' : u ∈ S'ᶜ := by
    intro huS'
    exact hu (hsubset huS')
  have hv' : v ∈ S'ᶜ := by
    intro hvS'
    exact hv (hsubset hvS')
  let H : SimpleGraph {z : V // z ∈ S'ᶜ} := G.induce S'ᶜ
  let T : Set {z : V // z ∈ S'ᶜ} :=
    {a | a.1 ∈ outsideComponent G S C}
  have huC : u ∈ outsideComponent G S C := by
    refine ⟨⟨u, hu⟩, ?_, rfl⟩
    change (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ = C
    rfl
  have hvNotC : v ∉ outsideComponent G S C := by
    rintro ⟨a, ha, hav⟩
    have hae : a = (⟨v, hv⟩ : {z : V // z ∈ Sᶜ}) :=
      Subtype.ext hav
    subst a
    exact hsep ha.symm
  have hAdjClosed : ∀ {a b : {z : V // z ∈ S'ᶜ}},
      a ∈ T → H.Adj a b → b ∈ T := by
    intro a b ha hab
    change a.1 ∈ outsideComponent G S C at ha
    change b.1 ∈ outsideComponent G S C
    have he : G.Adj a.1 b.1 := hab
    by_cases hbS : b.1 ∈ S
    · have hbEq : b.1 = s := by
        by_contra hne
        have hbS' : b.1 ∈ S' := by
          refine ⟨hbS, ?_⟩
          simpa using hne
        exact b.2 hbS'
      have hback : G.Adj s a.1 := by
        rw [← hbEq]
        exact he.symm
      exact (hno ⟨a.1, ha, hback⟩).elim
    · exact outsideComponent_adj G S C ha hbS he
  have hNoReach :
      ¬ H.Reachable
          (⟨u, hu'⟩ : {z : V // z ∈ S'ᶜ})
          (⟨v, hv'⟩ : {z : V // z ∈ S'ᶜ}) := by
    apply not_reachable_of_adj_closed H T hAdjClosed
    · exact huC
    · exact hvNotC
  have hsep' : SeparatesVertices G u v S' := by
    refine ⟨hu', hv', ?_⟩
    intro hEq
    exact hNoReach (SimpleGraph.ConnectedComponent.exact hEq)
  exact (hmin S' hproper) hsep'

/-- An inclusion-minimal u-v separator is essential on both
sides: every separator vertex has a neighbor in each of the
two distinguished endpoint components. -/
theorem minimal_separator_two_sided_neighbors
    (G : SimpleGraph V) (u v : V) (S : Set V)
    (hu : u ∈ Sᶜ) (hv : v ∈ Sᶜ)
    (hsep :
      (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ ≠
        (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩)
    (hmin : ∀ T : Set V, T ⊂ S →
      ¬ SeparatesVertices G u v T)
    (s : V) (hs : s ∈ S) :
    (∃ c : V, c ∈ outsideComponent G S
      ((G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩) ∧
      G.Adj s c) ∧
    (∃ d : V, d ∈ outsideComponent G S
      ((G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩) ∧
      G.Adj s d) := by
  constructor
  · exact minimal_separator_neighbor_endpoint
      G u v S hu hv hsep hmin s hs
  · have hminRev : ∀ T : Set V, T ⊂ S →
        ¬ SeparatesVertices G v u T := by
      intro T hT hSepT
      exact (hmin T hT)
        ((separatesVertices_comm G u v T).mpr hSepT)
    exact minimal_separator_neighbor_endpoint
      G v u S hv hu hsep.symm hminRev s hs

end TreeLike
end AllThoseEPPA
