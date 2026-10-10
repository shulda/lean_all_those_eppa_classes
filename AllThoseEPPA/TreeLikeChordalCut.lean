import AllThoseEPPA.TreeLikeChordalMinimalClique
import AllThoseEPPA.TreeLikeComponentCut
import AllThoseEPPA.TreeLikeEdgeCut

/-!
# A genuine irreducible free cut in the chordal case

This is the first recursive step of the paper's Lemma `lem:cuts`.
The proof combines the checked chordal minimal-separator theorem
with the checked structure-theoretic free-decomposition constructor.

If the distinguished E-reduct is chordal and every irreducible
substructure is an E-clique, then a pair of nonadjacent vertices
produces a proper free decomposition whose exact intersection is
a **closed irreducible substructure**. Crucially, the intersection
is the original minimal separator, not its (potentially larger)
functional closure.

The result is formulated without an EPPA action or an embedded copy
of A: these assumptions have already been compressed into
`IrreduciblesAreCliques`, and the statement will be reusable on
induced substructures during the tree-amalgamation induction.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}

/-- A nonedge in a finite chordal E-reduct produces an actual free
decomposition along a closed, irreducible separator.

Both sides are proper by the fields of `FreeDecomposition`;
moreover their intersection is *exactly* the chosen irreducible base.
No faithfulness or action parameter is needed for this formulation. -/
theorem exists_irreducible_free_cut_of_nonedge
    [Finite V]
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False)
    (u v : V) (hne : u ≠ v)
    (hnonedge : ¬ B.Edge E u v) :
    ∃ (S : Set V) (hS : B.IsClosed S),
      (B.induce S hS).IsIrreducible ∧
        ∃ d : B.FreeDecomposition, d.left ∩ d.right = S := by
  let G : SimpleGraph V := distinguishedGraph B E hloop hsymm
  have hNonAdj : ¬ G.Adj u v := hnonedge
  obtain ⟨S, ⟨hu, hv, hSep⟩, hMin⟩ :=
    exists_inclusion_minimal_separator G u v hne hNonAdj
  let C : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩
  let D : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩
  have hCD : C ≠ D := hSep
  have hS : B.IsClosed S :=
    minimal_separator_isClosed
      B E hIrred hloop hsymm u v S hu hv hSep hMin
  have hIrr : (B.induce S hS).IsIrreducible :=
    minimal_separator_isIrreducible
      B E hIrred hloop hsymm hNo u v S hu hv hSep hMin
  let X : Set V := componentCutLeft G S C
  let Y : Set V := componentCutRight G S C
  have hIntersection : X ∩ Y = S :=
    componentCut_inter G S C
  have hClosedIntersection : B.IsClosed (X ∩ Y) := by
    rw [hIntersection]
    exact hS
  have hCross :
      ∀ (x : V), x ∈ X → x ∉ Y →
        ∀ (y : V), y ∈ Y → y ∉ X → ¬ B.Edge E x y := by
    intro x hx hx' y hy hy'
    exact componentCut_no_cross G S C x hx hx' y hy hy'
  let d : B.FreeDecomposition :=
    freeDecomposition_of_closed_edge_separator
      B E hIrred hsymm X Y
      (componentCut_cover G S C)
      hClosedIntersection
      hCross
      (componentCutLeft_proper G S C
        (otherComponent_gives_vertex G S C D hCD.symm))
      (componentCutRight_proper G S C)
  refine ⟨S, hS, hIrr, d, ?_⟩
  change X ∩ Y = S
  exact hIntersection

/-- The dichotomy needed for induction: a finite chordal E-structure
with clique irreducibles is either itself E-complete, or decomposes
as a proper free amalgam over an irreducible induced substructure.

This is the completed *one-step* cut, not yet the iterated
tree-amalgamation of copies of A. -/
theorem edgeComplete_or_irreducible_free_cut
    [Finite V]
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False) :
    B.EdgeComplete E ∨
      ∃ (S : Set V) (hS : B.IsClosed S),
        (B.induce S hS).IsIrreducible ∧
          ∃ d : B.FreeDecomposition, d.left ∩ d.right = S := by
  classical
  by_cases hComplete : B.EdgeComplete E
  · exact Or.inl hComplete
  · right
    have hPair : ∃ u v : V, u ≠ v ∧ ¬ B.Edge E u v := by
      by_contra hNone
      apply hComplete
      intro x y
      constructor
      · intro hxy hEq
        subst y
        exact hloop x hxy
      · intro hxy
        by_contra hNot
        exact hNone ⟨x, y, hxy, hNot⟩
    obtain ⟨x, y, hne, hNon⟩ := hPair
    exact exists_irreducible_free_cut_of_nonedge
      B E hIrred hloop hsymm hNo x y hne hNon

end TreeLike
end AllThoseEPPA
