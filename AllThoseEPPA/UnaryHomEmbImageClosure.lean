import AllThoseEPPA.TreeLikeHomEmbClosedIrreducibleImage

/-!
# Global image closure of Γ-homomorphism-embeddings with unary functions

The proof of manuscript Theorem thm:main takes the image
of a forbidden homomorphism-embedding F→B and regards
that image as an actual function-closed induced substructure
of B. This is not true for general homomorphisms, and for
nonunary functions it need not follow from local exactness.

In a language of set-valued *unary* functions it DOES follow
from homomorphism-embedding: for each vertex x in the
image, choose a preimage a. The one-point function closure
cl_A(a) is irreducible, so the map is an exact embedding
there. Its image in B is closed. Since every unary function
input is exactly one vertex, this proves that the entire
image f(A) is function-closed.

This small result is the image-closure interface needed
when applying the local-size control of thm:maintree
to a forbidden homomorphism-embedding.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- The entire image of a Γ-homomorphism-embedding is
function-closed when every function symbol is unary.
No finiteness, global injectivity, or trivial Γ-action
assumptions are necessary. -/
theorem range_isClosed_of_unary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f) :
    B.IsClosed (Set.range f.toFun) := by
  classical
  intro n F xs hxs y hy
  have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
  subst n
  obtain ⟨a, ha⟩ := hxs 0
  let S : Set V := A.closureAtSet a
  let hS : A.IsClosed S := A.isClosed_closureSet {a}
  have hIrr : (A.induce S hS).IsIrreducible := by
    exact A.closureAt_isIrreducible a
  have hExact : IsEmbeddingOn act f S :=
    hf S hS hIrr
  have hImage : B.IsClosed (imageSet f.toFun S) :=
    image_isClosed_of_embeddingOn act f S hS hExact
  have hxsImage : ∀ i : Fin 1, xs i ∈ imageSet f.toFun S := by
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact ⟨a, A.mem_closureAtSet a, ha⟩
  obtain ⟨z, hz, hzy⟩ := hImage F xs hxsImage hy
  exact ⟨z, hzy⟩

end Homomorphism
end Structure
end AllThoseEPPA
