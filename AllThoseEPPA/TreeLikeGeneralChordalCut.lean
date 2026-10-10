import AllThoseEPPA.TreeLikeChordalMinimalClique
import AllThoseEPPA.TreeLikeComponentFree

/-!
# A closed clique separator gives a genuine free decomposition

This is the full *structural splitting step* of the induction in
the paper's Lemma `lem:cuts`, without assuming that the ambient
structure itself is an EPPA witness.

Suppose B is a finite structure with unary set-valued functions,
E is a symmetric loopless binary relation, every irreducible
substructure of B is an E-clique, and there are no induced E-cycles
of length at least four. Then any pair of distinct E-nonadjacent
vertices produces:
* an inclusion-minimal separator S of the E-graph,
* automatic function closure of S,
* an E-clique, hence irreducible, structure on S,
* and an actual free decomposition of B over precisely S.

Unlike earlier faithful-witness lemmas, this theorem is formulated
entirely with the hereditary local assumptions, so that it can be
reapplied recursively to proper induced substructures.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}

/-- The graph-theoretic and structural splitting conclusion of
`lem:cuts`, with an explicit closed clique amalgamation base. -/
theorem exists_closed_clique_free_cut_of_nonadjacent
    [Finite V]
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False)
    (u v : V) (huv : u ≠ v)
    (hNonadj : ¬ B.Edge E u v) :
    ∃ (S : Set V) (hS : B.IsClosed S),
      EdgeClique B E S ∧
      ∃ d : B.FreeDecomposition, d.left ∩ d.right = S := by
  let G : SimpleGraph V := distinguishedGraph B E hloop hsymm
  have hNoAdj : ¬ G.Adj u v := hNonadj
  obtain ⟨S, hSep, hMin⟩ :=
    exists_inclusion_minimal_separator G u v huv hNoAdj
  obtain ⟨hu, hv, hCD⟩ := hSep
  have hS : B.IsClosed S :=
    minimal_separator_isClosed B E hIrred hloop hsymm
      u v S hu hv hCD hMin
  have hClique : EdgeClique B E S :=
    minimal_separator_edgeClique B E hloop hsymm hNo
      u v S hu hv hCD hMin
  let C : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩
  let D : (G.induce Sᶜ).ConnectedComponent :=
    (G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩
  have hOther :
      ∃ y : V, y ∈ Sᶜ ∧ y ∉ outsideComponent G S C :=
    otherComponent_gives_vertex G S C D hCD.symm
  let X : Set V := componentCutLeft G S C
  let Y : Set V := componentCutRight G S C
  let d : B.FreeDecomposition :=
    freeDecomposition_of_closed_edge_separator B E
      hIrred hsymm X Y
      (componentCut_cover G S C)
      (by
        change B.IsClosed
          (componentCutLeft G S C ∩ componentCutRight G S C)
        rw [componentCut_inter G S C]
        exact hS)
      (by
        intro x hx hx' y hy hy'
        exact componentCut_no_cross G S C x hx hx' y hy hy')
      (componentCutLeft_proper G S C hOther)
      (componentCutRight_proper G S C)
  refine ⟨S, hS, hClique, d, ?_⟩
  exact componentCut_inter G S C

/-- In particular, the amalgamation base supplied by the
previous theorem is an irreducible induced substructure. -/
theorem exists_irreducible_base_free_cut_of_nonadjacent
    [Finite V]
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False)
    (u v : V) (huv : u ≠ v)
    (hNonadj : ¬ B.Edge E u v) :
    ∃ (S : Set V) (hS : B.IsClosed S),
      (B.induce S hS).IsIrreducible ∧
      ∃ d : B.FreeDecomposition, d.left ∩ d.right = S := by
  obtain ⟨S, hS, hc, d, hd⟩ :=
    exists_closed_clique_free_cut_of_nonadjacent B E
      hIrred hloop hsymm hNo u v huv hNonadj
  exact ⟨S, hS, closed_edgeClique_isIrreducible B E S hS hc,
    d, hd⟩

end TreeLike
end AllThoseEPPA
