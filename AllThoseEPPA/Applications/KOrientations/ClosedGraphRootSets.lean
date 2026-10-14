import AllThoseEPPA.Applications.KOrientations.ClosedGraphDegreeEquivalence

/-!
# Full reachable-root sets under isomorphisms of closed graph pieces

Closed induced graph isomorphisms preserve ambient paths and exact
root status. Hence they identify the entire reachable-root set of
every vertex, including roots reached via long paths. This is the
root-set part of the graph-determines-d-functions argument.

The source and target subsets need only be successor-closed.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Every path starting inside a successor-closed subset remains
entirely inside it, including its final vertex. -/
theorem reaches_mem_of_successor_closed
    {V : Type u} (G : Digraph V) (S : Set V)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    {x y : V} (hPath : G.Reaches x y) (hx : x ∈ S) :
    y ∈ S := by
  induction hPath with
  | refl x =>
      exact hx
  | @step x y z hEdge hRest ih =>
      exact ih (hS x y hx hEdge)

/-- Root status and reachability are both intrinsic to a
successor-closed graph piece. -/
theorem closedGraph_mem_roots_iff
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    (x r : S) :
    r.val ∈ G.roots k x.val ↔
      (e r).val ∈ H.roots k (e x).val := by
  change (G.IsRoot k r.val ∧ G.Reaches x.val r.val) ↔
    (H.IsRoot k (e r).val ∧
      H.Reaches (e x).val (e r).val)
  exact and_congr
    (closedGraph_isRoot_iff G H k S T hS hT e hEdge r)
    (reaches_iff_of_equiv_on_successor_closed
      G H S T hS hT e hEdge x r)

/-- Every reachable root of a point in S remains in S, and the
isomorphism carries its *complete* root set to the target root set. -/
theorem closedGraph_roots_image
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    (x : S) :
    H.roots k (e x).val =
      (fun r : S => (e r).val) ''
        {r : S | r.val ∈ G.roots k x.val} := by
  ext y
  constructor
  · rintro ⟨hRoot, hReaches⟩
    have hyT : y ∈ T :=
      reaches_mem_of_successor_closed H T hT hReaches (e x).property
    let r : S := e.symm ⟨y, hyT⟩
    have hEq : e r = (⟨y, hyT⟩ : T) :=
      e.apply_symm_apply ⟨y, hyT⟩
    have hMapped : (e r).val ∈ H.roots k (e x).val := by
      change H.IsRoot k (e r).val ∧
        H.Reaches (e x).val (e r).val
      simpa only [hEq] using
        (show H.IsRoot k y ∧ H.Reaches (e x).val y from
          ⟨hRoot, hReaches⟩)
    have hOriginal : r.val ∈ G.roots k x.val :=
      (closedGraph_mem_roots_iff G H k S T hS hT e hEdge x r).mpr
        hMapped
    exact ⟨r, hOriginal, congrArg Subtype.val hEq⟩
  · rintro ⟨r, hr, rfl⟩
    exact (closedGraph_mem_roots_iff G H k S T hS hT e hEdge x r).mp hr

end AllThoseEPPA.Applications.KOrientations
