import AllThoseEPPA.TreeLikeFreshBinaryStructure
import AllThoseEPPA.Irreducible

/-!
# Irreducibility and homomorphism-embeddings survive forgetting E

The unrestricted paper theorem needs to forget the auxiliary distinguished
binary relation after the fixed-E construction. A free decomposition of the
expanded structure is automatically a free decomposition of its reduct:
the old relation-locality and all exact function fibres are inherited.

Consequently, irreducibility of an old-language reduct implies
irreducibility of its expansion, even when the extra E has *arbitrary*
interpretation. A Γ-homomorphism-embedding of expanded structures
restricts to a Γ-homomorphism-embedding of old-language reducts
without assuming global injectivity.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable {Γ : Type x} [Group Γ]

/-- Induced substructures commute definitionally with deleting a relation
symbol; closure depends only on the unchanged set-valued function fibres. -/
@[simp] theorem forgetFixedBinary_induce
    (A : Structure L.withFixedBinaryRel V)
    (S : Set V) (hS : A.IsClosed S) :
    (A.induce S hS).forgetFixedBinary =
      A.forgetFixedBinary.induce S hS := rfl

namespace FreeDecomposition

/-- Deleting a relation symbol preserves every genuine free decomposition,
including closedness and the empty mixed-tuple function fibres. -/
def forgetFixedBinary
    {A : Structure L.withFixedBinaryRel V}
    (d : FreeDecomposition A) :
    FreeDecomposition A.forgetFixedBinary where
  left := d.left
  right := d.right
  left_closed := d.left_closed
  right_closed := d.right_closed
  cover := d.cover
  left_proper := d.left_proper
  right_proper := d.right_proper
  rel_local := by
    intro n R xs hx
    exact d.rel_local (.inl R) xs hx
  func_cross_empty := by
    intro n F xs hcross
    exact d.func_cross_empty F xs hcross

end FreeDecomposition

/-- A structure whose reduct is irreducible is irreducible even after adding
arbitrary extra binary-relation tuples: an extra relation cannot create a
new free decomposition. -/
theorem irreducible_of_forgetFixedBinary
    (A : Structure L.withFixedBinaryRel V)
    (hIrr : A.forgetFixedBinary.IsIrreducible) :
    A.IsIrreducible := by
  constructor
  intro d
  exact hIrr.false d.forgetFixedBinary

namespace Homomorphism

/-- A genuine Γ-homomorphism-embedding descends across deletion of E:
every closed irreducible old-language substructure is also irreducible
in the expanded language, where the local map is an exact embedding. -/
theorem forgetFixedBinary_isHomomorphismEmbedding
    (act : L.Action Γ)
    {A : Structure L.withFixedBinaryRel V}
    {B : Structure L.withFixedBinaryRel W}
    (f : Homomorphism act.withFixedBinaryRel A B)
    (hF : IsHomomorphismEmbedding act.withFixedBinaryRel f) :
    IsHomomorphismEmbedding act (f.forgetFixedBinary act) := by
  intro S hS hIrr
  have hIrrExpanded : (A.induce S hS).IsIrreducible :=
    irreducible_of_forgetFixedBinary (A.induce S hS) hIrr
  have hLocal := hF S hS hIrrExpanded
  refine ⟨hLocal.1, ?_, ?_⟩
  · intro n R xs hxs
    exact hLocal.2.1 (.inl R) xs hxs
  · intro n F xs hxs
    exact hLocal.2.2 F xs hxs

end Homomorphism
end Structure
end AllThoseEPPA
