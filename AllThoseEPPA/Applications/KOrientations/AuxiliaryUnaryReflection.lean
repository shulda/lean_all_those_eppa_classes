import AllThoseEPPA.Applications.KOrientations.AuxiliaryClosedRelationTransfer
import AllThoseEPPA.Applications.KOrientations.GraphPermutations

/-!
# Exact unary successor reflection on matching source-root pairs

The auxiliary B₁-language has a single unary set-valued successor
function. It is the restriction of directed reachability to source
root vertices. An actual graph automorphism g of B₀ preserves and
reflects every reachability pair, including paths of arbitrary length.

Together with the preceding relation-wise R_P/E_P reflection, this
completes the pointwise relation/function verification needed for
a partial auxiliary isomorphism on matching closed root domains.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Matching root points have matching auxiliary unary successor
incidence, with both implications. -/
theorem auxiliary_root_successor_transport_iff
    {V : Type u} [Fintype V] (G : Digraph V) (k : ℕ)
    (S : Set V) (g : G.graphAut)
    (x y x' y' : RootsIn G k S)
    (hx : x'.val = g.1 x.val)
    (hy : y'.val = g.1 y.val) :
    y ∈ (auxiliaryRootStructure G k S).func
        AuxiliaryFunc.successor ![x] ↔
      y' ∈ (auxiliaryRootStructure G k S).func
        AuxiliaryFunc.successor ![x'] := by
  change G.Reaches x.val y.val ↔ G.Reaches x'.val y'.val
  rw [hx, hy]
  exact (G.reaches_iff_perm g.1 g.2).symm

end AllThoseEPPA.Applications.KOrientations
