import AllThoseEPPA.Applications.KOrientations.ClosedGraphAllDFunctions
import AllThoseEPPA.Applications.KOrientations.StructureBridge
import AllThoseEPPA.Substructure

/-!
# Graph-determines-functions: exact closed d-piece isomorphisms

A directed graph isomorphism between two d-closed induced pieces is
automatically an exact isomorphism of their induced full d-structures:
not only edges and unary successors, but all root-fibre functions
of every positive finite arity.

The function values are genuine sets (not unary relational graphs).
Their exact preservation follows from the predecessor theorem
`closedGraph_dFunction_image`, whereas the d-closedness hypotheses
make the induced structures honest substructures. The resulting
embedding is bijective because the underlying carrier is an Equiv.

This is the general graph-determines-functions lemma, distinct from
and logically prior to EPPA extension/coherence.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Use the trivial action on the full d-language for graph-induced
structure maps. -/
def dTrivialAction : dLanguage.Action PUnit.{1} :=
  Language.Action.trivial dLanguage PUnit.{1}

/-- A closed-piece induced graph isomorphism gives a *bijective*,
function-exact d-structure embedding of the induced substructures. -/
noncomputable def closedGraph_inducedDIsomorphism
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hDS : G.IsDClosed k S)
    (hDT : H.IsDClosed k T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val) :
    Structure.Embedding dTrivialAction
      ((dStructure G k).induce S
        ((dStructure_isClosed_iff G k S).mpr hDS))
      ((dStructure H k).induce T
        ((dStructure_isClosed_iff H k T).mpr hDT)) where
  lang := 1
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro n R xs
    cases R with
    | edge =>
        change H.edge (e (xs 0)).val (e (xs 1)).val ↔
          G.edge (xs 0).val (xs 1).val
        exact (hEdge (xs 0) (xs 1)).symm
  map_func := by
    intro n F xs
    change e '' {z : S |
        z.val ∈ (dStructure G k).func F (fun i => (xs i).val)} =
      {z : T |
        z.val ∈ (dStructure H k).func F
          (fun i => (e (xs i)).val)}
    have hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S := by
      intro x y hx hxy
      exact hDS.1 x y hx (G.reaches_of_edge hxy)
    have hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T := by
      intro x y hx hxy
      exact hDT.1 x y hx (H.reaches_of_edge hxy)
    exact closedGraph_dFunction_image G H k S T
      hS hT e hEdge F xs

/-- The closed-piece embedding above is surjective as well as
injective, hence an isomorphism on the complete induced carriers. -/
theorem closedGraph_inducedDIsomorphism_bijective
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hDS : G.IsDClosed k S)
    (hDT : H.IsDClosed k T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val) :
    Function.Bijective
      (closedGraph_inducedDIsomorphism
        G H k S T hDS hDT e hEdge).toFun :=
  e.bijective

end AllThoseEPPA.Applications.KOrientations
