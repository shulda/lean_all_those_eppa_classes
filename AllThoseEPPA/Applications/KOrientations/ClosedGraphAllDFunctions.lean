import AllThoseEPPA.Applications.KOrientations.ClosedGraphDFiberEquivalence
import AllThoseEPPA.Applications.KOrientations.ClosedGraphSuccessorEquivalence

/-!
# Every d-function on a successor-closed graph piece is graph-determined

A graph isomorphism between successor-closed subsets identifies the
entire unary successor fibre and every finite root-set fibre.
Consequently its induced bijection identifies the *full set of
outputs within the two piece carriers* for every function symbol
of the infinite d-language.

This theorem does not silently identify the restricted value sets
with the ambient ones: d-closedness of the pieces ensures they agree
when this result is applied to actual substructures.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Exact transport of every restricted d-function value set, for
arbitrary arity and both function-symbol constructors. -/
theorem closedGraph_dFunction_image
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val)
    {n : ℕ} (F : DFunctionSymbol n) (xs : Fin n → S) :
    e '' {z : S |
        z.val ∈ (dStructure G k).func F (fun i => (xs i).val)} =
      {z : T |
        z.val ∈ (dStructure H k).func F
          (fun i => (e (xs i)).val)} := by
  cases F with
  | successor =>
      change e '' {z : S | z.val ∈ G.successors (xs 0).val} =
        {z : T | z.val ∈ H.successors (e (xs 0)).val}
      exact closedGraph_successors_image G H S T hS hT e hEdge (xs 0)
  | fiber n hpos =>
      change e '' {z : S |
          z.val ∈ G.dFiber k (fun i => (xs i).val)} =
        {z : T |
          z.val ∈ H.dFiber k (fun i => (e (xs i)).val)}
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (closedGraph_dFiber_iff G H k S T hS hT e hEdge
          xs w).mp hw
      · intro hz
        refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
        apply (closedGraph_dFiber_iff G H k S T hS hT e hEdge
          xs (e.symm z)).mpr
        change z.val ∈ H.dFiber k
          (fun i => (e (xs i)).val) at hz
        simpa only [e.apply_symm_apply] using hz

end AllThoseEPPA.Applications.KOrientations
