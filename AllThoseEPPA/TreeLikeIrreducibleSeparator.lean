import AllThoseEPPA.TreeLikeGraphInterface

/-!
# Closed E-cliques are irreducible amalgamation bases

The chordal-cut construction should never need to reconstruct the
irreducibility of a separator after it has become known to be a
closed E-clique: it follows directly from `cliqueClosure_isIrreducible`.

This module makes that implication explicit and exposes both the
structural and the Mathlib `SimpleGraph.IsClique` formulations.
These statements will become the amalgamation-base side condition
in the recursive tree-amalgamation construction for `lem:cuts`.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every *closed* E-clique is an irreducible induced substructure.
No assumption on the arities of set-valued functions is required. -/
theorem closed_edgeClique_isIrreducible
    (B : Structure L V) (E : L.RelSymbol 2)
    (S : Set V) (hS : B.IsClosed S)
    (hclique : EdgeClique B E S) :
    (B.induce S hS).IsIrreducible := by
  have h := cliqueClosure_isIrreducible B E S hclique
  simpa only [Structure.closureStructure,
    B.closureSet_eq_self hS] using h

/-- Equivalently, a closed clique in the Mathlib simple graph
associated with E is irreducible as a structure. -/
theorem closed_graphClique_isIrreducible
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (S : Set V) (hS : B.IsClosed S)
    (hclique : (distinguishedGraph B E hloop hsymm).IsClique S) :
    (B.induce S hS).IsIrreducible :=
  closed_edgeClique_isIrreducible B E S hS
    ((edgeClique_iff_graphClique B E hloop hsymm S).mpr hclique)

end TreeLike
end AllThoseEPPA
