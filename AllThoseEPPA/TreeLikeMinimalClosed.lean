import AllThoseEPPA.TreeLikeEssentialNeighbors
import AllThoseEPPA.TreeLikeTwoSidedClosure

/-!
# Minimal vertex separators are automatically closed under unary functions

The paper's proof of `lem:cuts` replaces a minimal graph separator
by its closure under the functions. In the irreducible-clique regime
this extra step is unnecessary. Every vertex of a minimal u-v
separator has neighbors in both endpoint components, and this
forces all its unary-function values to stay in the separator.

This lemma packages the checked graph and structure results and
isolates the still-open theorem: `S` is an E-clique when G has no
induced cycles of length at least four. When that assertion is
proved, the minimal separator will also be an irreducible
amalgamation base.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}

/-- In a unary-function structure with irreducible E-cliques,
every inclusion-minimal separator between two distinct vertices
of the distinguished graph is closed under all functions.
No chordality hypothesis is needed. -/
theorem minimal_separator_isClosed
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
        (distinguishedGraph B E hloop hsymm) u v T) :
    B.IsClosed S := by
  let G : SimpleGraph V := distinguishedGraph B E hloop hsymm
  let C : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩
  let D : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩
  have hBoth : ∀ x ∈ S,
      (∃ c : V, c ∈ outsideComponent G S C ∧ B.Edge E x c) ∧
      (∃ d : V, d ∈ outsideComponent G S D ∧ B.Edge E x d) := by
    intro x hx
    exact minimal_separator_two_sided_neighbors
      G u v S hu hv hsep hmin x hx
  exact two_sided_separator_isClosed
    B E hIrred hloop hsymm S C D hsep hBoth

end TreeLike
end AllThoseEPPA
