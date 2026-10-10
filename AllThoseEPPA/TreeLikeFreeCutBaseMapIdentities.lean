import AllThoseEPPA.TreeLikeFreeCutBaseEmbeddings

/-!
# Exact vertex identities for factored free-cut interface embeddings

The previous checked `Embedding.factorThrough` constructs a
genuine Γ-embedding whenever its image lies in another
embedding's range. This file supplies the elementary but
crucial pointwise identity: factoring g through j does not
change the composite into the shared ambient structure.

Applied to the two inclusions of a `FreeDecomposition`,
this shows that the shared-base embeddings defined previously
are literally the canonical inclusions of vertices into the
left and right induced side. Hence their values in the ambient
structure agree on every common vertex, with no unverified
identification between nested subtype carriers.
-/

namespace AllThoseEPPA
namespace Structure
namespace Embedding

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x} {X : Type y}

/-- The factoring construction satisfies the defining
vertex-level equality with the ambient embedding. -/
theorem factorThrough_apply_spec
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    {C : Structure L X}
    (j : Embedding act A B)
    (g : Embedding act C B)
    (hRange : ∀ c : X, ∃ a : V, j a = g c)
    (c : X) :
    j (j.factorThrough act g hRange c) = g c := by
  change j (Classical.choose (hRange c)) = g c
  exact Classical.choose_spec (hRange c)

end Embedding
end Structure

namespace TreeLike

universe u v w
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w}

/-- The base-to-left embedding sends each vertex to the same
ambient vertex (with a different subtype proof). -/
theorem freeCut_baseToLeft_val
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    (s : d.left ∩ d.right) :
    (freeCut_baseToLeft act B d s).1 = s.1 := by
  change
    (Structure.inclusion act B d.left d.left_closed)
        (freeCut_baseToLeft act B d s) =
      (Structure.inclusion act B (d.left ∩ d.right)
        (freeCut_base_isClosed B d)) s
  exact Structure.Embedding.factorThrough_apply_spec act
    (Structure.inclusion act B d.left d.left_closed)
    (Structure.inclusion act B (d.left ∩ d.right)
      (freeCut_base_isClosed B d))
    (by intro x; exact ⟨⟨x.1, x.2.1⟩, rfl⟩) s

/-- The corresponding right inclusion is equally literal
on the underlying vertices. -/
theorem freeCut_baseToRight_val
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    (s : d.left ∩ d.right) :
    (freeCut_baseToRight act B d s).1 = s.1 := by
  change
    (Structure.inclusion act B d.right d.right_closed)
        (freeCut_baseToRight act B d s) =
      (Structure.inclusion act B (d.left ∩ d.right)
        (freeCut_base_isClosed B d)) s
  exact Structure.Embedding.factorThrough_apply_spec act
    (Structure.inclusion act B d.right d.right_closed)
    (Structure.inclusion act B (d.left ∩ d.right)
      (freeCut_base_isClosed B d))
    (by intro x; exact ⟨⟨x.1, x.2.2⟩, rfl⟩) s

/-- The two exact Γ-embeddings of the common base describe
one and the same original vertex, as required for pushout
gluing along this base. -/
theorem freeCut_baseToSides_agree_on_vertices
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    (s : d.left ∩ d.right) :
    (freeCut_baseToLeft act B d s).1 =
      (freeCut_baseToRight act B d s).1 := by
  rw [freeCut_baseToLeft_val, freeCut_baseToRight_val]

end TreeLike
end AllThoseEPPA
