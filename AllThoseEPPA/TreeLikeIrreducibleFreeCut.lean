import AllThoseEPPA.TreeLikeComponentFree
import AllThoseEPPA.TreeLikeIrreducibleSeparator

/-!
# Free decompositions whose amalgamation base is irreducible

The classical proof of `lem:cuts` requires a *genuine free
decomposition* with an irreducible overlap. A general closed graph
separator of a faithful E-witness yields the former; if the
separator is an E-clique, the previously formalized clique-closure
lemma yields the latter.

This file packages those two facts, including the technical point
that the intersection of closed substructures is closed and the
overlap of the component-cut decomposition is exactly the given
separator. No chordality is needed here; the graph-theoretic
chordal minimal-separator theorem will provide the clique premise.
-/

namespace AllThoseEPPA
namespace Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The intersection of two closed substructures is closed, for
set-valued functions of any arity. -/
theorem isClosed_inter
    (B : Structure L V) (S T : Set V)
    (hS : B.IsClosed S) (hT : B.IsClosed T) :
    B.IsClosed (S ∩ T) := by
  intro n F xs hxs y hy
  exact ⟨hS F xs (fun i => (hxs i).1) hy,
    hT F xs (fun i => (hxs i).2) hy⟩

namespace FreeDecomposition

/-- The amalgamation base of a free decomposition is a
closed substructure of the ambient structure. -/
def baseClosed (B : Structure L V)
    (d : B.FreeDecomposition) :
    B.IsClosed (d.left ∩ d.right) :=
  B.isClosed_inter d.left d.right d.left_closed d.right_closed

/-- The amalgamation base itself is irreducible. This is
the key inductive side condition for tree amalgamations. -/
def HasIrreducibleBase (B : Structure L V)
    (d : B.FreeDecomposition) : Prop :=
  (B.induce (d.left ∩ d.right) (baseClosed B d)).IsIrreducible

end FreeDecomposition
end Structure

namespace TreeLike

universe u v w z
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {α : Type w} {β : Type z}

/-- A closed E-clique S with two distinct outside components
produces a free decomposition of the finite faithful witness
whose amalgamation base is irreducible. The decomposition
is explicit, not merely a cover of the E graph. -/
theorem exists_freeDecomposition_irreducibleBase_of_cliqueCut
    (act : L.Action Γ)
    (A : Structure L α) (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ)
    (S : Set β) (hS : B.IsClosed S)
    (hClique : EdgeClique B E S)
    (C D :
      ((faithfulGraph act A B ψ E hfix hcomplete hfaith).induce Sᶜ).ConnectedComponent)
    (hCD : C ≠ D) :
    ∃ d : B.FreeDecomposition,
      Structure.FreeDecomposition.HasIrreducibleBase B d := by
  let G := faithfulGraph act A B ψ E hfix hcomplete hfaith
  let d : B.FreeDecomposition :=
    freeDecomposition_of_two_components
      act A B ψ E hfix hcomplete hfaith S hS C D hCD
  have hbase : d.left ∩ d.right = S := by
    change componentCutLeft G S C ∩ componentCutRight G S C = S
    exact componentCut_inter G S C
  have hirr : (B.induce S hS).IsIrreducible :=
    closed_edgeClique_isIrreducible B E S hS hClique
  refine ⟨d, ?_⟩
  unfold Structure.FreeDecomposition.HasIrreducibleBase
  change (B.induce (d.left ∩ d.right)
    (Structure.FreeDecomposition.baseClosed B d)).IsIrreducible
  rw [hbase]
  exact hirr

end TreeLike
end AllThoseEPPA
