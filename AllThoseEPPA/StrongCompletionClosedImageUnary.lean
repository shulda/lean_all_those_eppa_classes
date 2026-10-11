import AllThoseEPPA.UnaryHomEmbImageClosure
import AllThoseEPPA.TreeLikeHomEmbComposition

/-!
# Images of arbitrary closed pieces under unary homomorphism-embeddings

For set-valued unary functions, the range of an arbitrary
Γ-homomorphism-embedding is closed. The same is true of
the image of *every* function-closed induced substructure.

This will be needed to apply strong amalgamation inside a
hereditary completion class: the common interface of two
completed sides is the ACTUAL induced structure on the image
of the central closed region C, not the original C with
possibly missing relations.

The argument restricts the homomorphism-embedding to A|S,
reuses the general composition theorem, then invokes the
already checked entire-range closure lemma. No global
injectivity or finite carrier is needed.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- The image of ANY function-closed S⊆A under a
Γ-homomorphism-embedding is function-closed in B.

Exact reflection is assumed only on irreducible pieces,
not on the whole S. -/
theorem image_closedSet_isClosed_of_unary
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (S : Set V) (hS : A.IsClosed S) :
    B.IsClosed (imageSet f.toFun S) := by
  let j : Embedding act (A.induce S hS) A :=
    Structure.inclusion act A S hS
  let h : Homomorphism act (A.induce S hS) B :=
    f.comp j.toHomomorphism
  have hj : IsHomomorphismEmbedding act j.toHomomorphism :=
    Embedding.toHomomorphism_isHomomorphismEmbedding act j
  have hh : IsHomomorphismEmbedding act h :=
    comp_isHomomorphismEmbedding act f j.toHomomorphism hf hj
  have hRange : B.IsClosed (Set.range h.toFun) :=
    h.range_isClosed_of_unary act hh
  have hEq : Set.range h.toFun = imageSet f.toFun S := by
    ext b
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.1, x.2, hx⟩
    · rintro ⟨x, hx, hfx⟩
      exact ⟨⟨x, hx⟩, hfx⟩
  rw [hEq] at hRange
  exact hRange

end Homomorphism
end Structure
end AllThoseEPPA
