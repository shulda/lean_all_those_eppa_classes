import AllThoseEPPA.TreeLikeMinimalClosed
import AllThoseEPPA.TreeLikeIrreducibleSeparator

/-!
# A clique minimal separator is an irreducible amalgamation base

All graph-separator ingredients of `lem:cuts`, apart from the
actual chordal-graph clique theorem, now fit together:

1. An inclusion-minimal separator between two vertices in a
   symmetric loopless E-reduct is closed under unary functions,
   provided all irreducibles are E-cliques.
2. If the separator is an E-clique, its induced *substructure* is
   irreducible.

This module packages both into a single interface for the
tree-amalgamation induction. Its remaining assumption is exactly
the chordal clique-separator assertion, not an additional closure
axiom or hypothesis.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}

/-- An E-clique that is also an inclusion-minimal vertex
separator is automatically a *closed, irreducible substructure*.
The proof no longer needs to form its functional closure as a
separate step. -/
theorem minimal_separator_clique_isIrreducible
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (u v : V) (S : Set V)
    (hu : u ∈ Sᶜ) (hv : v ∈ Sᶜ)
    (hsep :
      ((distinguishedGraph B E hloop hsymm).induce Sᶜ).connectedComponentMk
        ⟨u, hu⟩ ≠
      ((distinguishedGraph B E hloop hsymm).induce Sᶜ).connectedComponentMk
        ⟨v, hv⟩)
    (hmin : ∀ T : Set V, T ⊂ S →
      ¬ SeparatesVertices
        (distinguishedGraph B E hloop hsymm) u v T)
    (hclique :
      (distinguishedGraph B E hloop hsymm).IsClique S) :
    ∃ hS : B.IsClosed S, (B.induce S hS).IsIrreducible := by
  have hS : B.IsClosed S :=
    minimal_separator_isClosed B E hIrred hloop hsymm
      u v S hu hv hsep hmin
  exact ⟨hS,
    closed_graphClique_isIrreducible B E hloop hsymm S hS hclique⟩

end TreeLike
end AllThoseEPPA
