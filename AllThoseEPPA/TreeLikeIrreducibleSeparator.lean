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
  constructor
  intro d
  have hCliqueU :
      EdgeClique (B.induce S hS) E (Set.univ : Set S) := by
    intro x y _ _ hne
    have hneq : (x : V) ≠ (y : V) := by
      intro heq
      exact hne (Subtype.ext heq)
    have hedge : B.Edge E x.1 y.1 :=
      hclique x.2 y.2 hneq
    change B.rel E (Subtype.val ∘ Structure.pairTuple x y)
    rw [Structure.pairTuple_map]
    exact hedge
  rcases edgeClique_subset_one_side
      (B.induce S hS) E d Set.univ hCliqueU with hl | hr
  · apply d.left_proper
    apply Set.eq_univ_of_forall
    intro x
    exact hl (Set.mem_univ x)
  · apply d.right_proper
    apply Set.eq_univ_of_forall
    intro x
    exact hr (Set.mem_univ x)

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
