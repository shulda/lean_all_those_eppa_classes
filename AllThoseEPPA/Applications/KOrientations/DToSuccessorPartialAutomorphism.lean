import AllThoseEPPA.Applications.KOrientations.ClosedGraphDInducedIso
import AllThoseEPPA.Applications.KOrientations.StructureBridge
import AllThoseEPPA.EPPA

/-!
# Exact forgetful partial automorphisms from d-closures to unary successors

The input d-expansion of a finite k-orientation has genuine
n-ary set-valued root-fibre symbols for ALL positive arities.
The first coherent EPPA theorem acts on its unary-successor
reduct, not directly on this non-unary language.

Every honest partial d-automorphism has closed source/target,
so these sets are successor-closed too. Its exact edge
reflection and exact preservation of the unary successor
function survive forgetting all the higher-arity F_n.
This constructs the ACTUAL checked Structure.PartialAutomorphism
needed by the first coherent EPPA selector.

The language actions are both trivial, so no hidden symbol
relabeling choice occurs; the underlying PartialEquiv, including
its actual source/target and its chosen outside-domain total
functions, is retained word-for-word. Coherent selection/gluing
is not asserted in this file.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- A genuine full d-partial automorphism restricts to an honest
partial isomorphism of the unary-successor language, preserving
the exact partial equivalence of vertices and all set-valued
successor fibres. -/
noncomputable def dPartialAutomorphism_to_successor
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure G k)) :
    Structure.PartialAutomorphism successorAction (successorStructure G) where
  lang := 1
  toPartialEquiv := p.toPartialEquiv
  source_closed := by
    apply (successorStructure_isClosed_iff G p.source).2
    exact ((dStructure_isClosed_iff G k p.source).1 p.source_closed).1
  target_closed := by
    apply (successorStructure_isClosed_iff G p.target).2
    exact ((dStructure_isClosed_iff G k p.target).1 p.target_closed).1
  map_rel_iff := by
    intro n R xs hxs
    cases R with
    | edge =>
        change G.edge (p (xs 0)) (p (xs 1)) ↔
          G.edge (xs 0) (xs 1)
        exact p.map_rel_iff EdgeSymbol.edge xs hxs
  map_func := by
    intro n F xs hxs
    cases F with
    | successor =>
        change Structure.imageSet p.toPartialEquiv
            (G.successors (xs 0)) =
          G.successors (p (xs 0))
        exact p.map_func DFunctionSymbol.successor xs hxs

/-- Forgetting higher-arity fibres does not change the exact
source domain of the original partial d-automorphism. -/
@[simp] theorem dPartialAutomorphism_to_successor_source
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure G k)) :
    (dPartialAutomorphism_to_successor G k p).source = p.source :=
  rfl

/-- Nor does it change the target domain. -/
@[simp] theorem dPartialAutomorphism_to_successor_target
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure G k)) :
    (dPartialAutomorphism_to_successor G k p).target = p.target :=
  rfl

/-- Pointwise this is LITERALLY the same mathematical partial
map, including the outside-domain fallback convention. -/
@[simp] theorem dPartialAutomorphism_to_successor_apply
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure G k))
    (x : V) :
    (dPartialAutomorphism_to_successor G k p) x = p x :=
  rfl

end AllThoseEPPA.Applications.KOrientations
