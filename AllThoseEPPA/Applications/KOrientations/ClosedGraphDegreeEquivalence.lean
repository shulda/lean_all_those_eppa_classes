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
  refine
    { toFun := fun y => ⟨(e (toS y)).val, ?_⟩
      invFun := fun z => ⟨(e.symm (toT z)).val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (H.mem_outNeighbors (e x).val _).mpr
    exact (hEdge x (toS y)).mp
      ((G.mem_outNeighbors x.val y.val).mp y.property)
  · apply (G.mem_outNeighbors x.val _).mpr
    have h := (hEdge x (e.symm (toT z))).mpr
    have heq : e (e.symm (toT z)) = toT z :=
      e.apply_symm_apply (toT z)
    have hz : H.edge (e x).val (toT z).val :=
      (H.mem_outNeighbors (e x).val z.val).mp z.property
    exact h (by simpa only [heq] using hz)
  · intro y
    apply Subtype.ext
    change (e.symm (toT ⟨(e (toS y)).val, _⟩)).val = y.val
    have he : toT ⟨(e (toS y)).val, _⟩ = e (toS y) :=
      Subtype.ext rfl
    rw [he, e.symm_apply_apply]
    rfl
  · intro z
    apply Subtype.ext
    change (e (toS ⟨(e.symm (toT z)).val, _⟩)).val = z.val
    have he : toS ⟨(e.symm (toT z)).val, _⟩ = e.symm (toT z) :=
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
