import AllThoseEPPA.Applications.KOrientations.Graph
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card

/-!
# Graph permutation transport for the root-sort construction

A permutation preserving directed edges preserves every path,
the exact outdegree, root status, and the complete set of reachable
roots. These results will supply the Γ-action on R_P / E_P symbols
without choosing lifts from a quotient of the template automorphism group.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

namespace Digraph

variable {V : Type u} [Fintype V] (G : Digraph V)

/-- A directed graph permutation maps its complete outneighbourhood
bijectively to the outneighbourhood of the image vertex. -/
noncomputable def outNeighborsEquivOfPerm
    (g : Equiv.Perm V)
    (hEdge : ∀ x y, G.edge (g x) (g y) ↔ G.edge x y)
    (x : V) :
    (G.outNeighbors x) ≃ (G.outNeighbors (g x)) := by
  classical
  refine
    { toFun := fun y => ⟨g y.1, ?_⟩
      invFun := fun y => ⟨g.symm y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (G.mem_outNeighbors (g x) (g y.1)).2
      ((hEdge x y.1).2 ((G.mem_outNeighbors x y.1).1 y.2))
  · apply (G.mem_outNeighbors x (g.symm y.1)).2
    apply (hEdge x (g.symm y.1)).1
    simpa only [g.apply_symm_apply] using
      ((G.mem_outNeighbors (g x) y.1).1 y.2)
  · intro y
    apply Subtype.ext
    exact g.symm_apply_apply y.1
  · intro y
    apply Subtype.ext
    exact g.apply_symm_apply y.1

/-- Directed graph automorphisms preserve exact outdegree. -/
theorem outdegree_eq_of_perm
    (g : Equiv.Perm V)
    (hEdge : ∀ x y, G.edge (g x) (g y) ↔ G.edge x y)
    (x : V) :
    (G.outNeighbors (g x)).card = (G.outNeighbors x).card := by
  classical
  have hcard := Fintype.card_congr
    (G.outNeighborsEquivOfPerm g hEdge x)
  simpa only [Fintype.card_coe] using hcard.symm

/-- Whether a vertex is a root is invariant under graph permutations. -/
theorem isRoot_iff_perm (k : ℕ)
    (g : Equiv.Perm V)
    (hEdge : ∀ x y, G.edge (g x) (g y) ↔ G.edge x y)
    (x : V) :
    G.IsRoot k (g x) ↔ G.IsRoot k x := by
  change (G.outNeighbors (g x)).card < k ↔
    (G.outNeighbors x).card < k
  rw [G.outdegree_eq_of_perm g hEdge x]

/-- Edge-preserving permutations transport reflexive directed paths. -/
theorem reaches_of_perm
    (g : Equiv.Perm V)
    (hEdge : ∀ x y, G.edge (g x) (g y) ↔ G.edge x y)
    {x y : V} (h : G.Reaches x y) :
    G.Reaches (g x) (g y) := by
  induction h with
  | refl x =>
      exact Digraph.Reaches.refl (g x)
  | step h _ ih =>
      exact Digraph.Reaches.step ((hEdge _ _).2 h) ih

/-- The converse path transport uses the inverse permutation. -/
theorem reaches_iff_perm
    (g : Equiv.Perm V)
    (hEdge : ∀ x y, G.edge (g x) (g y) ↔ G.edge x y)
    {x y : V} :
    G.Reaches (g x) (g y) ↔ G.Reaches x y := by
  have hInverse :
      ∀ a b, G.edge (g.symm a) (g.symm b) ↔ G.edge a b := by
    intro a b
    have h := hEdge (g.symm a) (g.symm b)
    simpa only [g.apply_symm_apply] using h.symm
  constructor
  · intro h
    have hBack := G.reaches_of_perm g.symm hInverse h
    simpa only [g.symm_apply_apply] using hBack
  · exact G.reaches_of_perm g hEdge

/-- Graph automorphisms preserve the entire reachable-root set. -/
theorem roots_image_of_perm (k : ℕ)
    (g : Equiv.Perm V)
    (hEdge : ∀ x y, G.edge (g x) (g y) ↔ G.edge x y)
    (x : V) :
    G.roots k (g x) = g '' G.roots k x := by
  ext z
  constructor
  · intro hz
    refine ⟨g.symm z, ⟨?_, ?_⟩, g.apply_symm_apply z⟩
    · apply (G.isRoot_iff_perm k g hEdge (g.symm z)).1
      simpa only [g.apply_symm_apply] using hz.1
    · apply (G.reaches_iff_perm g hEdge).1
      simpa only [g.apply_symm_apply] using hz.2
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(G.isRoot_iff_perm k g hEdge r).2 hr.1,
      (G.reaches_iff_perm g hEdge).2 hr.2⟩

end Digraph
end AllThoseEPPA.Applications.KOrientations
