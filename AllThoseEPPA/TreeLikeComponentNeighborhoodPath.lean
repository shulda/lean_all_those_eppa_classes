import AllThoseEPPA.TreeLikeInducedAmbientPath
import AllThoseEPPA.TreeLikeComponentPaths

/-!
# Chordless paths between separator vertices via an outside component

If u has a neighbor c in a connected component C of G induced outside
S and v has a neighbor d in the same C, there is a path from u to v
whose vertices lie in C or are u,v themselves. Choosing that path in
the graph induced on {u,v} ∪ C and then using the induced-ambient-path
interface makes it a chordless path of the *ambient graph*, without
having to remove endpoint chords from a concatenated walk.

This is the exact geometric input for proving minimal separators in
chordal graphs are cliques.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- The permissible support of a path connecting u,v via C. -/
def componentPathDomain (G : SimpleGraph V)
    (S : Set V) (C : (G.induce Sᶜ).ConnectedComponent)
    (u v : V) : Set V :=
  {x | x = u ∨ x = v ∨ x ∈ outsideComponent G S C}

/-- Two endpoints adjacent to the same outside component admit a
chordless path that stays in that component except at its endpoints. -/
theorem exists_chordless_path_through_component
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (u v : V)
    (hUC : ∃ c : V, c ∈ outsideComponent G S C ∧ G.Adj u c)
    (hDV : ∃ d : V, d ∈ outsideComponent G S C ∧ G.Adj d v) :
    ∃ p : G.Walk u v,
      p.IsPath ∧ p.IsChordless ∧
        (∀ x ∈ p.support,
          x = u ∨ x = v ∨ x ∈ outsideComponent G S C) := by
  obtain ⟨c, hc, huc⟩ := hUC
  obtain ⟨d, hd, hdv⟩ := hDV
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  obtain ⟨d₀, hd₀, rfl⟩ := hd
  let T : Set V := componentPathDomain G S C u v
  have huT : u ∈ T := Or.inl rfl
  have hvT : v ∈ T := Or.inr (Or.inl rfl)
  let f : C.toSimpleGraph →g G.induce T :=
    { toFun := fun w => ⟨(w.1.1 : V), Or.inr
          (Or.inr (componentVertex_mem_outsideComponent G S C w))⟩
      map_rel' := by
        intro a b hab
        exact hab }
  let a : C := ⟨c₀, hc₀⟩
  let b : C := ⟨d₀, hd₀⟩
  have habReach : C.toSimpleGraph.Reachable a b :=
    C.reachable_toSimpleGraph a.property b.property
  have hTReach : (G.induce T).Reachable (f a) (f b) :=
    habReach.map f
  have hFirst : (G.induce T).Adj (⟨u, huT⟩ : T) (f a) := by
    change G.Adj u (c₀ : V)
    exact huc
  have hLast : (G.induce T).Adj (f b) (⟨v, hvT⟩ : T) := by
    change G.Adj (d₀ : V) v
    exact hdv
  have hUVReach : (G.induce T).Reachable
      (⟨u, huT⟩ : T) (⟨v, hvT⟩ : T) :=
    (hFirst.reachable.trans hTReach).trans hLast.reachable
  obtain ⟨p, hpPath, hpChord, hpT⟩ :=
    exists_chordless_ambient_path_of_induced_reachable
      G T u v huT hvT hUVReach
  exact ⟨p, hpPath, hpChord, hpT⟩

end TreeLike
end AllThoseEPPA
