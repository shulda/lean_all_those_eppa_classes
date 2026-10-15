import AllThoseEPPA.Applications.KOrientations.AuxiliaryPartialRelations
import AllThoseEPPA.Applications.KOrientations.GraphPermutations

/-!
# Exact unary function reflection for the auxiliary root partial map

Besides R_P and E_P relation iff, the second-stage partial
isomorphism must transport the set-valued unary successor function
*exactly*. Since the auxiliary function is directed reachability
on roots of the first-stage graph, this follows from the graph
automorphism's two-sided transport of paths.

We express the statement on individual source/target root vertices;
the later partial-equivalence API will package these iff conditions
with the actual closed source/target domains.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Exact preservation and reflection of membership in unary
auxiliary successor values under an actual graph automorphism. -/
theorem auxiliaryRootStructure_successor_transport_iff
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (g : G.graphAut)
    (x y r s : RootsIn G k S)
    (hy : y.val = g.1 x.val)
    (hs : s.val = g.1 r.val) :
    r ∈ (auxiliaryRootStructure G k S).func
      AuxiliaryFunc.successor ![x] ↔
    s ∈ (auxiliaryRootStructure G k S).func
      AuxiliaryFunc.successor ![y] := by
  change G.Reaches x.val r.val ↔ G.Reaches y.val s.val
  rw [hy, hs]
  exact (G.reaches_iff_perm g.1 g.2).symm

end AllThoseEPPA.Applications.KOrientations
