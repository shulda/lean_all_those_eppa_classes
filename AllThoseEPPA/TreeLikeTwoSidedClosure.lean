import AllThoseEPPA.TreeLikeFunctionEdge
import AllThoseEPPA.TreeLikeComponentCut
import AllThoseEPPA.UnaryFunctions

/-!
# Two-sided clique separators are closed under unary functions

Let E be a symmetric simple graph relation and suppose every
irreducible closed substructure is an E-clique. If each vertex of
a separator S has an E-neighbor in each of two distinct connected
components of the graph outside S, then S is automatically closed
under every unary set-valued function.

The key is the previously formalized `function_value_adjacent_to_edge_endpoint`:
if s is adjacent to c, every function value z of s is also adjacent
to c unless it coincides with c. Thus an output z outside S would lie
in *both* components that have a neighbor of s, impossible.

This statement does not itself assert that a minimal vertex separator
has the required neighbors; that remains the next graph-theoretic lemma.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}

/-- If a function value z of x lies outside S, then it lies in every
component of the E-reduct outside S that contains a neighbor of x. -/
theorem function_value_mem_neighbor_component
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (S : Set V)
    (C : ((distinguishedGraph B E hloop hsymm).induce Sᶜ).ConnectedComponent)
    {n : ℕ} (F : L.FuncSymbol n)
    (x z c : V)
    (hz : z ∈ B.func F (fun _ => x))
    (hzS : z ∈ Sᶜ)
    (hc : c ∈ outsideComponent
      (distinguishedGraph B E hloop hsymm) S C)
    (hxc : B.Edge E x c) :
    z ∈ outsideComponent
      (distinguishedGraph B E hloop hsymm) S C := by
  let G := distinguishedGraph B E hloop hsymm
  by_cases hzc : z = c
  · subst z
    exact hc
  · have hezc : B.Edge E z c :=
      function_value_adjacent_to_edge_endpoint
        B E hIrred F x c z hxc hz hzc
    have hecz : G.Adj c z := by
      change B.Edge E c z
      exact (hsymm z c).mp hezc
    exact outsideComponent_adj G S C hc hzS hecz

/-- If every separator vertex has a neighbor in each of two
distinct components outside the separator, the separator is
closed under all unary set-valued functions. -/
theorem two_sided_separator_isClosed
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (S : Set V)
    (C D : ((distinguishedGraph B E hloop hsymm).induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D)
    (hBoth : ∀ x ∈ S,
      (∃ c : V, c ∈ outsideComponent
        (distinguishedGraph B E hloop hsymm) S C ∧ B.Edge E x c) ∧
      (∃ d : V, d ∈ outsideComponent
        (distinguishedGraph B E hloop hsymm) S D ∧ B.Edge E x d)) :
    B.IsClosed S := by
  classical
  intro n F xs hxs z hz
  let x := xs (UnaryFunctions.unaryIndex F)
  have hxS : x ∈ S := hxs (UnaryFunctions.unaryIndex F)
  have htuple : xs = fun _ => x :=
    UnaryFunctions.unaryTuple_eq_constant F xs
  rw [htuple] at hz
  by_contra hzS
  have hzOut : z ∈ Sᶜ := hzS
  obtain ⟨⟨c, hc, hxc⟩, ⟨d, hd, hxd⟩⟩ := hBoth x hxS
  let G := distinguishedGraph B E hloop hsymm
  have hzC : z ∈ outsideComponent G S C :=
    function_value_mem_neighbor_component B E hIrred
      hloop hsymm S C F x z c hz hzOut hc hxc
  have hzD : z ∈ outsideComponent G S D :=
    function_value_mem_neighbor_component B E hIrred
      hloop hsymm S D F x z d hz hzOut hd hxd
  obtain ⟨a, ha, hza⟩ := hzC
  obtain ⟨b, hb, hzb⟩ := hzD
  have hab : a = b := Subtype.ext (hza.trans hzb.symm)
  subst b
  have hEq : C = D :=
    SimpleGraph.ConnectedComponent.eq_of_common_vertex ha hb
  exact hCD hEq

end TreeLike
end AllThoseEPPA
