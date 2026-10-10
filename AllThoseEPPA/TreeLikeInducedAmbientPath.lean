import AllThoseEPPA.TreeLikeChordlessShortest
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Chordless paths in induced graphs remain chordless in the ambient graph

The separator-clique proof needs paths chosen in a graph induced on
the union of one outside component and the two separator endpoints.
An induced path of this restricted graph is also an induced path in
the ambient graph, since induced graphs reflect adjacency.

The original walk is mapped along the canonical graph embedding of
the induced graph into the ambient graph. We prove preservation of
both `IsPath` and `IsChordless`, and that the resulting walk's
vertices all remain inside the given set.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- Canonical inclusion of an induced subgraph as a graph homomorphism. -/
def inducedInclusion (G : SimpleGraph V) (T : Set V) :
    G.induce T →g G :=
  (SimpleGraph.Embedding.induce (G := G) T).toHom

@[simp] theorem inducedInclusion_apply
    (G : SimpleGraph V) (T : Set V) (x : T) :
    inducedInclusion G T x = (x : V) :=
  rfl

/-- The inclusion preserves chordlessness, because adjacency
between images of vertices is reflected by the induced graph. -/
theorem chordless_map_inducedInclusion
    (G : SimpleGraph V) (T : Set V)
    {a b : T} (p : (G.induce T).Walk a b)
    (hp : p.IsChordless) :
    (p.map (inducedInclusion G T)).IsChordless := by
  classical
  apply SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mpr
  intro x y hx hy hxy
  have hxMap : x ∈ p.support.map (inducedInclusion G T) := by
    simpa only [SimpleGraph.Walk.support_map] using hx
  have hyMap : y ∈ p.support.map (inducedInclusion G T) := by
    simpa only [SimpleGraph.Walk.support_map] using hy
  obtain ⟨x0, hx0, hxx⟩ := List.mem_map.mp hxMap
  obtain ⟨y0, hy0, hyy⟩ := List.mem_map.mp hyMap
  have hAdj : (G.induce T).Adj x0 y0 := by
    change G.Adj (x0 : V) (y0 : V)
    simpa only [inducedInclusion_apply] using
      (show G.Adj (inducedInclusion G T x0)
        (inducedInclusion G T y0) from by
          simpa only [hxx, hyy] using hxy)
  have hEdge : s(x0,y0) ∈ p.edges :=
    (SimpleGraph.Walk.isChordless_iff_forall_mem_edges.mp hp)
      hx0 hy0 hAdj
  rw [SimpleGraph.Walk.edges_map]
  apply List.mem_map.mpr
  refine ⟨s(x0,y0), hEdge, ?_⟩
  simpa only [Sym2.map_mk, inducedInclusion_apply, hxx, hyy]

/-- The induced-graph inclusion sends paths to paths. -/
theorem isPath_map_inducedInclusion
    (G : SimpleGraph V) (T : Set V)
    {a b : T} (p : (G.induce T).Walk a b)
    (hp : p.IsPath) :
    (p.map (inducedInclusion G T)).IsPath := by
  exact hp.map (by
    intro x y h
    exact Subtype.val_injective h)

/-- All vertices in a mapped induced-graph walk belong to the
original vertex set T. -/
theorem map_inducedInclusion_support
    (G : SimpleGraph V) (T : Set V)
    {a b : T} (p : (G.induce T).Walk a b) :
    ∀ x ∈ (p.map (inducedInclusion G T)).support, x ∈ T := by
  intro x hx
  have hxMap : x ∈ p.support.map (inducedInclusion G T) := by
    simpa only [SimpleGraph.Walk.support_map] using hx
  obtain ⟨a0, _, hax⟩ := List.mem_map.mp hxMap
  rw [← hax]
  exact a0.2

/-- Every reachable pair in an induced graph has an ambient
chordless path entirely inside the inducing vertex set. -/
theorem exists_chordless_ambient_path_of_induced_reachable
    (G : SimpleGraph V) (T : Set V)
    (u v : V) (hu : u ∈ T) (hv : v ∈ T)
    (hr : (G.induce T).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    ∃ p : G.Walk u v,
      p.IsPath ∧ p.IsChordless ∧
        (∀ x ∈ p.support, x ∈ T) := by
  obtain ⟨p, hpPath, hpChord⟩ :=
    exists_chordless_path (G.induce T) hr
  let q : G.Walk u v := p.map (inducedInclusion G T)
  exact ⟨q, isPath_map_inducedInclusion G T p hpPath,
    chordless_map_inducedInclusion G T p hpChord,
    map_inducedInclusion_support G T p⟩

end TreeLike
end AllThoseEPPA
