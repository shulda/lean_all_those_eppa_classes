import AllThoseEPPA.TreeLikeFaithfulClique

/-!
# Unary function values and the closure of a realized edge

The proof of `lem:cuts` must show that clique separators in the
distinguished graph are closed under all unary set-valued functions.

A useful stronger local fact follows solely from irreducibility of
relation-tuple closures: if x-y is a realized E-edge, and z is a
unary-function value of x, then z and y must be E-adjacent whenever
z ≠ y. Indeed, the closure of the E-tuple (x,y) is irreducible and
contains all such function values, hence is an E-clique.

This local statement is one of the key ingredients for the next
proof that a vertex separator whose vertices have neighbors in two
different components is automatically closed.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A unary-function value at x is E-adjacent to the other endpoint
of every E-edge x-y, provided the two vertices are distinct.
This works without even assuming E symmetric or loopless. -/
theorem function_value_adjacent_to_edge_endpoint
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    {n : ℕ} (F : L.FuncSymbol n)
    (x y z : V)
    (hxy : B.Edge E x y)
    (hz : z ∈ B.func F (fun _ => x))
    (hzy : z ≠ y) :
    B.Edge E z y := by
  let xs : Fin 2 → V := Structure.pairTuple x y
  let S : Set V := B.closureSet (Set.range xs)
  have hclosed : B.IsClosed S :=
    B.isClosed_closureSet (Set.range xs)
  have hIrredS : (B.induce S hclosed).IsIrreducible :=
    B.relationTupleClosure_isIrreducible E xs hxy
  have hxS : x ∈ S := by
    apply B.subset_closureSet (Set.range xs)
    exact ⟨(0 : Fin 2), by simp [xs, Structure.pairTuple]⟩
  have hyS : y ∈ S := by
    apply B.subset_closureSet (Set.range xs)
    exact ⟨(1 : Fin 2), by simp [xs, Structure.pairTuple]⟩
  have hzS : z ∈ S :=
    hclosed F (fun _ => x) (fun _ => hxS) hz
  exact (hIrred S hclosed hIrredS) hzS hyS hzy

end TreeLike
end AllThoseEPPA
