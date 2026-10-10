import AllThoseEPPA.TreeLikeChordlessShortest
import AllThoseEPPA.TreeLikeComponentCut

/-!
# Induced paths through a connected component outside a separator

For any component C of the graph induced on Sᶜ and any two vertices
of C, connectivity provides a walk *inside C*. The shortest-walk
theorem improves this to an induced (chordless) path inside C.

The carrier is the subtype C, not the ambient vertex type. Hence
every vertex of the resulting path is guaranteed to lie in the
selected outside component, a property essential for combining
paths through different components in the clique-separator proof.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u
variable {V : Type u}

/-- Every vertex of a component carries a certificate that its
underlying ambient vertex lies in `outsideComponent`. -/
theorem componentVertex_mem_outsideComponent
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (w : C) :
    (w.1 : V) ∈ outsideComponent G S C :=
  ⟨w.1, w.2, rfl⟩

/-- Inside an outside component, every two vertices are joined by
a chordless path. All intermediate vertices are in that component
by construction, without an ambient-level path-avoidance argument. -/
theorem exists_chordless_component_path
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (a b : C) :
    ∃ p : C.toSimpleGraph.Walk a b,
      p.IsPath ∧ p.IsChordless ∧
      (∀ w ∈ p.support, (w.1 : V) ∈ outsideComponent G S C) := by
  obtain ⟨p, hp, hch⟩ :=
    exists_chordless_path C.toSimpleGraph
      (C.reachable_toSimpleGraph a.2 b.2)
  refine ⟨p, hp, hch, ?_⟩
  intro w hw
  exact componentVertex_mem_outsideComponent G S C w

/-- A formulation on the original vertex type, suitable for
starting with the neighbor witnesses supplied by a minimal
separator. The path is still typed in the component and hence
does not leave that component. -/
theorem exists_component_path_between_ambient_vertices
    (G : SimpleGraph V) (S : Set V)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (a b : V)
    (ha : a ∈ outsideComponent G S C)
    (hb : b ∈ outsideComponent G S C) :
    ∃ (a' b' : C) (p : C.toSimpleGraph.Walk a' b'),
      (a'.1 : V) = a ∧ (b'.1 : V) = b ∧
      p.IsPath ∧ p.IsChordless := by
  obtain ⟨a0, ha0, rfl⟩ := ha
  obtain ⟨b0, hb0, rfl⟩ := hb
  let a' : C := ⟨a0, ha0⟩
  let b' : C := ⟨b0, hb0⟩
  obtain ⟨p, hp, hch, _⟩ :=
    exists_chordless_component_path G S C a' b'
  exact ⟨a', b', p, rfl, rfl, hp, hch⟩

end TreeLike
end AllThoseEPPA
