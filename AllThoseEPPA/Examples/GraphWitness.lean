import AllThoseEPPA.Examples.Graph

/-!
# The valuation witness for finite graphs

This is the witness construction from Section 3 of the paper.

The paper writes a valuation at `x` as a function on `A \ {x}`.  In Lean
we use an equivalent total Boolean-valued function on `A` whose value at
`x` is forced to be false.  This avoids dependent-domain transports when a
permutation moves the base vertex.
-/

namespace AllThoseEPPA
namespace Graph

universe u

/-- A vertex `(x, χ)` of the graph EPPA witness.

The condition `χ x = false` is the Lean encoding of the paper's convention
that `χ` is only defined away from `x`. -/
structure WitnessVertex (α : Type u) where
  base : α
  valuation : α → Bool
  self_false : valuation base = false

namespace WitnessVertex

variable {α : Type u}

/-- The graph `B` of the warm-up construction: two valuation vertices are
adjacent exactly when their base vertices are distinct and their two
cross-valuations disagree. -/
def witnessGraph (α : Type u) : SimpleGraph (WitnessVertex α) where
  Adj v w :=
    v.base ≠ w.base ∧
      v.valuation w.base ≠ w.valuation v.base
  symm := by
    intro v w h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    intro v h
    exact h.1 rfl

@[simp] theorem witnessGraph_adj (v w : WitnessVertex α) :
    (witnessGraph α).Adj v w ↔
      v.base ≠ w.base ∧
        v.valuation w.base ≠ w.valuation v.base :=
  Iff.rfl

end WitnessVertex

section GenericCopy

variable {α : Type u} [LinearOrder α]

/-- The asymmetric adjacency row used for the generic copy of `G`.

It is true at `y` exactly when `y < x` and `{x,y}` is an edge. -/
def genericValuation (G : SimpleGraph α) (x y : α) : Bool :=
  decide (y < x ∧ G.Adj x y)

@[simp] theorem genericValuation_self (G : SimpleGraph α) (x : α) :
    genericValuation G x x = false := by
  simp [genericValuation]

/-- The generic-copy vertex corresponding to `x`. -/
def genericVertex (G : SimpleGraph α) (x : α) : WitnessVertex α where
  base := x
  valuation := genericValuation G x
  self_false := genericValuation_self G x

@[simp] theorem genericVertex_base (G : SimpleGraph α) (x : α) :
    (genericVertex G x).base = x :=
  rfl

/-- The generic copy has exactly the same adjacency relation as the original
graph. -/
theorem witnessGraph_adj_genericVertex_iff (G : SimpleGraph α) (x y : α) :
    (WitnessVertex.witnessGraph α).Adj
        (genericVertex G x) (genericVertex G y) ↔
      G.Adj x y := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hnyx : ¬ y < x := (asymm hxy)
    simp [WitnessVertex.witnessGraph_adj, genericVertex, genericValuation,
      hxy, hnyx, G.adj_comm]
  · simp [WitnessVertex.witnessGraph_adj, genericVertex, genericValuation]
  · have hnxy : ¬ x < y := (asymm hyx)
    simp [WitnessVertex.witnessGraph_adj, genericVertex, genericValuation,
      hyx, hnxy, G.adj_comm]

/-- The paper's map `ψ : A → B`, as an embedding in the general
`Γ_L`-structure API. -/
def genericEmbedding (G : SimpleGraph α) :
    Structure.Embedding action (toStructure G)
      (toStructure (WitnessVertex.witnessGraph α)) where
  lang := 1
  toFun := genericVertex G
  injective := by
    intro x y h
    exact congrArg WitnessVertex.base h
  map_rel_iff := by
    intro n R x
    cases R with
    | edge =>
      simpa using
        (witnessGraph_adj_genericVertex_iff G (x 0) (x 1))
  map_func := by
    intro n F x
    exact Empty.elim F

@[simp] theorem genericEmbedding_apply (G : SimpleGraph α) (x : α) :
    genericEmbedding G x = genericVertex G x :=
  rfl

end GenericCopy

end Graph
end AllThoseEPPA
