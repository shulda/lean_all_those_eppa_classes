import AllThoseEPPA.Applications.KOrientations.ClosedGraphPathEquivalence
import AllThoseEPPA.Applications.KOrientations.Encoding

/-!
# Exact unary successor values on closed graph pieces

An induced graph isomorphism between two successor-closed vertex sets
preserves and reflects the *whole* reachability relation in the ambient
digraphs. Therefore it transports the set-valued unary successor
function exactly, on the corresponding closed-piece carriers.

No bounded-degree, rootedness, non-unary function, or EPPA hypothesis
is necessary at this point.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The induced graph isomorphism identifies the successor-value sets
on its source and target subtype carriers, not just individual edges. -/
theorem closedGraph_successors_image
    {V : Type u} {W : Type v}
    (G : Digraph V) (H : Digraph W)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    (x : S) :
    e '' {y : S | y.val ∈ G.successors x.val} =
      {z : T | z.val ∈ H.successors (e x).val} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change H.Reaches (e x).val (e y).val
    exact (reaches_iff_of_equiv_on_successor_closed
      G H S T hS hT e hEdge x y).mp hy
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    change G.Reaches x.val (e.symm z).val
    apply (reaches_iff_of_equiv_on_successor_closed
      G H S T hS hT e hEdge x (e.symm z)).mpr
    change H.Reaches (e x).val z.val at hz
    simpa only [e.apply_symm_apply] using hz

/-- Equivalently, a closed induced graph isomorphism transports the
restricted value sets of the actual d-language unary successor symbol. -/
theorem closedGraph_dSuccessor_image
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    (x : S) :
    e '' {y : S |
      y.val ∈ (dStructure G k).func DFunctionSymbol.successor
        (fun _ : Fin 1 => x.val)} =
      {z : T |
        z.val ∈ (dStructure H k).func DFunctionSymbol.successor
          (fun _ : Fin 1 => (e x).val)} := by
  change e '' {y : S | y.val ∈ G.successors x.val} =
    {z : T | z.val ∈ H.successors (e x).val}
  exact closedGraph_successors_image G H S T hS hT e hEdge x

end AllThoseEPPA.Applications.KOrientations
