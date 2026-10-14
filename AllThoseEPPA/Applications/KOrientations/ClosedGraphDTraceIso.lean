import AllThoseEPPA.Applications.KOrientations.ClosedGraphDInducedIso

/-!
# Graph-determined d-traces without an ambient d-closedness assumption

The original source S in B₀ is known to be *successor-closed*,
but need not be d-closed in the ambient d-expansion of B₀.
It would therefore be an unjustified strengthening to require
G.IsDClosed k S merely to formalize its intrinsic d-structure.

Define the canonical d-trace on an arbitrary subset S: relations are
the restricted graph relations and every d-function value is the
intersection of its ambient value set with S. When S is genuinely
d-closed this is definitionally the usual induced substructure.

Between successor-closed pieces, a graph isomorphism preserves and
reflects every restricted d-function, including F_n for *all* arities.
The exact d-trace isomorphism requires no ambient d-closedness.
This is the appropriate interface for the embedded original source.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The canonical restricted d-language on a vertex set, whether or
not that set is closed under all ambient d-functions. -/
noncomputable def dTraceStructure
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V) :
    Structure dLanguage S where
  rel := by
    intro n R xs
    exact (dStructure G k).rel R (Subtype.val ∘ xs)
  func := by
    intro n F xs
    exact {z : S |
      z.val ∈ (dStructure G k).func F (Subtype.val ∘ xs)}

/-- On a genuinely d-closed set this agrees exactly with the
general EPPA library's induced substructure. -/
theorem dTraceStructure_eq_induce_of_dClosed
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hS : G.IsDClosed k S) :
    dTraceStructure G k S =
      (dStructure G k).induce S
        ((dStructure_isClosed_iff G k S).mpr hS) :=
  rfl

/-- A bijective induced graph map between successor-closed sets is an
exact embedding of their complete canonical d-traces, independently
of whether either is d-closed in the ambient graph. -/
noncomputable def closedGraph_dTraceEmbedding
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val) :
    Structure.Embedding dTrivialAction
      (dTraceStructure G k S)
      (dTraceStructure H k T) where
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
        z.val ∈ (dStructure G k).func F
          (fun i => (xs i).val)} =
      {z : T |
        z.val ∈ (dStructure H k).func F
          (fun i => (e (xs i)).val)}
    exact closedGraph_dFunction_image
      G H k S T hS hT e hEdge F xs

/-- The d-trace embedding is a genuine isomorphism on carriers. -/
theorem closedGraph_dTraceEmbedding_bijective
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : Digraph V) (H : Digraph W) (k : ℕ)
    (S : Set V) (T : Set W)
    (hS : ∀ (x y : V), x ∈ S → G.edge x y → y ∈ S)
    (hT : ∀ (x y : W), x ∈ T → H.edge x y → y ∈ T)
    (e : S ≃ T)
    (hEdge : ∀ x y : S,
      G.edge x.val y.val ↔ H.edge (e x).val (e y).val) :
    Function.Bijective
      (closedGraph_dTraceEmbedding G H k S T
        hS hT e hEdge).toFun :=
  e.bijective

end AllThoseEPPA.Applications.KOrientations
