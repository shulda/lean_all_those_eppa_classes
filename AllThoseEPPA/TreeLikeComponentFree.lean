import AllThoseEPPA.TreeLikeComponentCut

/-!
# Graph components of a closed separator produce free amalgam cuts

This connects the general graph-theoretic component partition
(`TreeLikeComponentCut`) with the already verified structure-theoretic
lemma that closed graph separators give free decompositions
(`TreeLikeFaithfulGraph`).

The conclusion is an actual `Structure.FreeDecomposition` object,
including the closure of both sides under unary set-valued functions.
No chordality assumption is used here: it will be needed in the next
step to *find* a closed clique separator, not to split along one.

Consequently, once a suitable closed clique separator is discovered
by chordal graph theory, this construction supplies the first
free-amalgamation step of the tree-amalgamation induction.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w z
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type z}

/-- If deleting a closed vertex set S leaves another component
besides a chosen component C, then the faithful witness admits
a free decomposition along S. The graph is obtained canonically
from the fixed complete E relation in the faithful witness. -/
noncomputable def freeDecomposition_of_componentCut
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (S : Set β) (hS : B.IsClosed S)
    (C : ((faithfulGraph act A B ψ E hfix hcomplete hfaith).induce Sᶜ).ConnectedComponent)
    (hOther : ∃ y : β, y ∈ Sᶜ ∧
      y ∉ outsideComponent
        (faithfulGraph act A B ψ E hfix hcomplete hfaith) S C) :
    B.FreeDecomposition := by
  let G : SimpleGraph β :=
    faithfulGraph act A B ψ E hfix hcomplete hfaith
  let X : Set β := componentCutLeft G S C
  let Y : Set β := componentCutRight G S C
  apply freeDecomposition_of_faithful_edge_separator
      act A B ψ E hfix hcomplete hfaith X Y
  · exact componentCut_cover G S C
  · change B.IsClosed
      (componentCutLeft G S C ∩ componentCutRight G S C)
    rw [componentCut_inter G S C]
    exact hS
  · intro x hx hx' y hy hy'
    have h : ¬ G.Adj x y :=
      componentCut_no_cross G S C x hx hx' y hy hy'
    simpa [G, faithfulGraph, distinguishedGraph] using h
  · exact componentCutLeft_proper G S C hOther
  · exact componentCutRight_proper G S C

/-- A more directly applicable variant: two different components
of the graph after deleting S yield a genuine free decomposition.
This isolates the exact graph-theoretic obligation needed in
the induction step of `lem:cuts`. -/
noncomputable def freeDecomposition_of_two_components
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (S : Set β) (hS : B.IsClosed S)
    (C D : ((faithfulGraph act A B ψ E hfix hcomplete hfaith).induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D) :
    B.FreeDecomposition :=
  freeDecomposition_of_componentCut
    act A B ψ E hfix hcomplete hfaith S hS C
    (otherComponent_gives_vertex
      (faithfulGraph act A B ψ E hfix hcomplete hfaith)
      S C D hCD.symm)

end TreeLike
end AllThoseEPPA
