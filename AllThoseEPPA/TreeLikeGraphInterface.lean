import Mathlib.Combinatorics.SimpleGraph.Clique
import AllThoseEPPA.TreeLikeFaithfulGraph

/-!
# From the distinguished relation E to a Mathlib simple graph

The remaining genuinely graph-theoretic part of Lemma `lem:cuts`
uses chordal graph theory and clique separators. We therefore expose
the auxiliary relation E as a genuine `SimpleGraph` using the
symmetry/looplessness already obtained from faithfulness.

This is a definitional bridge, not an assumption that the graph is
chordal. The latter must be proved from absence of induced cycles in
the independent graph-theory portion of the formalization.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w z
variable {L : Language.{u}} {V : Type v}

/-- The simple graph carried by a symmetric, loopless
distinguished binary relation. -/
def distinguishedGraph
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E) : SimpleGraph V where
  Adj := B.Edge E
  symm := by
    intro x y h
    exact (hsymm x y).mp h
  loopless := by
    intro x h
    exact hloop x h

@[simp] theorem distinguishedGraph_adj
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E) (x y : V) :
    (distinguishedGraph B E hloop hsymm).Adj x y ↔ B.Edge E x y :=
  Iff.rfl

/-- Our structural clique predicate agrees exactly with Mathlib's
notion of a clique in the associated simple graph. -/
theorem edgeClique_iff_graphClique
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E) (C : Set V) :
    EdgeClique B E C ↔
      (distinguishedGraph B E hloop hsymm).IsClique C :=
  Iff.rfl

variable {Γ : Type w} [Group Γ] {α : Type z}

/-- The distinguished graph on an irreducible-structure faithful
witness with E complete and fixed on A. -/
def faithfulGraph
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L V)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ) :
    SimpleGraph V :=
  distinguishedGraph B E
    (edgeLoopless_of_faithful act A B ψ E hfix hcomplete hfaith)
    (edgeSymmetric_of_faithful act A B ψ E hfix hcomplete hfaith)

@[simp] theorem faithfulGraph_adj
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L V)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (x y : V) :
    (faithfulGraph act A B ψ E hfix hcomplete hfaith).Adj x y ↔
      B.Edge E x y :=
  Iff.rfl

/-- Every irreducible substructure is a clique in the actual
Mathlib graph of the faithful witness. -/
theorem faithfulGraph_irreducible_isClique
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L V)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (S : Set V) (hS : B.IsClosed S)
    (hirr : (B.induce S hS).IsIrreducible) :
    (faithfulGraph act A B ψ E hfix hcomplete hfaith).IsClique S := by
  have hc : EdgeClique B E S :=
    irreduciblesAreCliques_of_faithful
      act A B ψ E hfix hcomplete hfaith S hS hirr
  exact (edgeClique_iff_graphClique B E _ _ S).mp hc

end TreeLike
end AllThoseEPPA
