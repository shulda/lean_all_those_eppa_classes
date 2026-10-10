import AllThoseEPPA.TreeLikeEmbeddingFactor
import AllThoseEPPA.TreeLikeEmbeddingRangeClosure
import AllThoseEPPA.Irreducible

/-!
# Exact common-base embeddings for a free decomposition

For the last induction step of manuscript Lemma `lem:cuts`, the
common interface is not an arbitrary overlap of two vertex sets:
it is the closed induced structure on the **exact** intersection
of the two sides of a genuine `FreeDecomposition`.

This file constructs genuine Γ-structure embeddings of the base
into both induced sides. Rather than silently identifying nested
subtypes or proving preservation of set-valued functions again,
we apply the previously checked factorization theorem to the
three canonical inclusion embeddings into the original ambient
structure.

The result works for relation symbols and set-valued function
symbols of arbitrary arity, with no unary restrictions.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}

/-- The exact common interface of any free decomposition is
closed under every function symbol. -/
theorem freeCut_base_isClosed
    (B : Structure L V) (d : B.FreeDecomposition) :
    B.IsClosed (d.left ∩ d.right) :=
  Structure.IsClosed.inter B d.left d.right
    d.left_closed d.right_closed

/-- The structure induced on the **actual intersection** of
the two sides, with closedness certified by both side
closedness witnesses. -/
def freeCut_base
    (B : Structure L V) (d : B.FreeDecomposition) :
    Structure L (d.left ∩ d.right) :=
  B.induce (d.left ∩ d.right) (freeCut_base_isClosed B d)

/-- Exact Γ-embedding from the common closed interface into
the left induced side of a genuine free decomposition.
The embedding is obtained by factoring the ambient base
inclusion through the ambient left-side inclusion. -/
noncomputable def freeCut_baseToLeft
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition) :
    Structure.Embedding act (freeCut_base B d)
      (B.induce d.left d.left_closed) :=
  (Structure.inclusion act B d.left d.left_closed).factorThrough act
    (Structure.inclusion act B (d.left ∩ d.right)
      (freeCut_base_isClosed B d))
    (by
      intro x
      exact ⟨⟨x.1, x.2.1⟩, rfl⟩)

/-- Exact Γ-embedding of the same common interface into
the right induced side. Both maps embed the *same* base,
which is essential when constructing the genuine Γ-pushout. -/
noncomputable def freeCut_baseToRight
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition) :
    Structure.Embedding act (freeCut_base B d)
      (B.induce d.right d.right_closed) :=
  (Structure.inclusion act B d.right d.right_closed).factorThrough act
    (Structure.inclusion act B (d.left ∩ d.right)
      (freeCut_base_isClosed B d))
    (by
      intro x
      exact ⟨⟨x.1, x.2.2⟩, rfl⟩)

end TreeLike
end AllThoseEPPA
