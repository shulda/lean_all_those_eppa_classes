import AllThoseEPPA.TreeLikeTwoSidedClosure
import AllThoseEPPA.TreeLikeComponentFree

/-!
# From a two-sided vertex separator to a genuine free decomposition

The preceding checked lemmas established independently that:
(1) a separator whose vertices have neighbors in two different
outside components is automatically closed under unary functions,
and (2) a closed separator with two outside components induces a
free decomposition of an irreducible-structure faithful EPPA witness.

This module packages their composition into a paper-facing
constructor, making the closedness hypothesis entirely automatic.
It will be directly applicable once the separate graph-theoretic
proof shows that minimal vertex separators have the required
two-sided adjacency.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w z
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type z}

/-- Two different components outside a vertex set S, together with
the property that every separator vertex is adjacent to both, give
a real free decomposition of an irreducible-faithful witness.
No separate function-closure hypothesis is needed. -/
noncomputable def freeDecomposition_of_two_sided_neighbors
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (S : Set β)
    (C D : ((faithfulGraph act A B ψ E hfix hcomplete hfaith).induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D)
    (hBoth : ∀ x ∈ S,
      (∃ c : β, c ∈ outsideComponent
        (faithfulGraph act A B ψ E hfix hcomplete hfaith) S C ∧ B.Edge E x c) ∧
      (∃ d : β, d ∈ outsideComponent
        (faithfulGraph act A B ψ E hfix hcomplete hfaith) S D ∧ B.Edge E x d)) :
    B.FreeDecomposition := by
  have hIrred : IrreduciblesAreCliques B E :=
    irreduciblesAreCliques_of_faithful
      act A B ψ E hfix hcomplete hfaith
  have hloop : B.EdgeLoopless E :=
    edgeLoopless_of_faithful
      act A B ψ E hfix hcomplete hfaith
  have hsymm : B.EdgeSymmetric E :=
    edgeSymmetric_of_faithful
      act A B ψ E hfix hcomplete hfaith
  have hS : B.IsClosed S :=
    two_sided_separator_isClosed B E hIrred hloop hsymm
      S C D hCD hBoth
  exact freeDecomposition_of_two_components
    act A B ψ E hfix hcomplete hfaith S hS C D hCD

end TreeLike
end AllThoseEPPA
