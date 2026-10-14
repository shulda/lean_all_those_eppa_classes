import AllThoseEPPA.Applications.KOrientations.ClosedGraphPathEquivalence
import Mathlib.Data.Fintype.Card

/-!
# Root status is absolute under successor-closed graph isomorphisms

An induced directed graph isomorphism between successor-closed
subsets identifies the *entire* outgoing neighbourhood of a vertex.
It therefore identifies outdegrees and the k-root predicate (defined
by outdegree < k), rather than merely preserving a distinguished
external unary root label. This will be needed to transfer all d-fibres.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- An edge-preserving bijection of successor-closed pieces restricts
to a bijection of the *ambient* outgoing neighbourhoods. -/
noncomputable def closedGraph_outNeighborsEquiv
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    (x : S) :
    (G.outNeighbors x.val) ≃ (H.outNeighbors (e x).val) := by
  classical
  let toS : (G.outNeighbors x.val) → S :=
    fun y => ⟨y.val,
      hS x.val y.val x.property
        ((G.mem_outNeighbors x.val y.val).mp y.property)⟩
  let toT : (H.outNeighbors (e x).val) → T :=
    fun y => ⟨y.val,
      hT (e x).val y.val (e x).property
        ((H.mem_outNeighbors (e x).val y.val).mp y.property)⟩
  let F : (G.outNeighbors x.val) → (H.outNeighbors (e x).val) :=
    fun y => ⟨(e (toS y)).val,
      (H.mem_outNeighbors (e x).val _).mpr
        ((hEdge x (toS y)).mp
          ((G.mem_outNeighbors x.val y.val).mp y.property))⟩
  let R : (H.outNeighbors (e x).val) → (G.outNeighbors x.val) :=
    fun z => by
      let t : S := e.symm (toT z)
      have hImage : e t = toT z :=
        e.apply_symm_apply (toT z)
      have hz : H.edge (e x).val (toT z).val :=
        (H.mem_outNeighbors (e x).val z.val).mp z.property
      have hEdgeH : H.edge (e x).val (e t).val := by
        rw [hImage]
        exact hz
      exact ⟨t.val,
        (G.mem_outNeighbors x.val _).mpr
          ((hEdge x t).mpr hEdgeH)⟩
  refine
    { toFun := F
      invFun := R
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    apply Subtype.ext
    change (e.symm (toT (F y))).val = y.val
    have he : toT (F y) = e (toS y) :=
      Subtype.ext rfl
    rw [he, e.symm_apply_apply]
    rfl
  · intro z
    apply Subtype.ext
    change (e (toS (R z))).val = z.val
    have he : toS (R z) = e.symm (toT z) :=
      Subtype.ext rfl
    rw [he, e.apply_symm_apply]
    rfl

/-- Exact outdegree is invariant under isomorphism of closed pieces. -/
theorem closedGraph_outdegree_eq
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    (x : S) :
    (G.outNeighbors x.val).card =
      (H.outNeighbors (e x).val).card := by
  classical
  let equiv := closedGraph_outNeighborsEquiv G H S T hS hT e hEdge x
  have hcard := Fintype.card_congr equiv
  simpa only [Fintype.card_coe] using hcard

/-- The k-root predicate is preserved and reflected, since the graph
isomorphism identifies all outgoing neighbours, not a subset of them. -/
theorem closedGraph_isRoot_iff
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    (x : S) :
    G.IsRoot k x.val ↔ H.IsRoot k (e x).val := by
  change (G.outNeighbors x.val).card < k ↔
    (H.outNeighbors (e x).val).card < k
  rw [closedGraph_outdegree_eq G H S T hS hT e hEdge x]

end AllThoseEPPA.Applications.KOrientations
