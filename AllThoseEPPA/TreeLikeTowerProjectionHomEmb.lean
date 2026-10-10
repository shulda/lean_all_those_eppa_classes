import AllThoseEPPA.TreeLikeTowerInducedProjectionHom
import AllThoseEPPA.TreeLikeInducedIrreducibles

/-!
# Heredity of homomorphism-embedding through closed-image induction

A homomorphism-embedding is not necessarily injective on its
whole carrier. Its defining property is that it is an
**exact embedding on every closed irreducible substructure**.
This property passes to restriction onto any closed induced
domain and its closed direct image.

The proof uses the checked nested-induced-irreducibility
transport and the ambient embedding-on-an-irreducible
hypothesis. In particular, it proves full *equality* of
set-valued function fibres on the irreducible pieces, not
merely homomorphism inclusion.

Consequently, each concrete canonical cycle-sparsening
projection between the closed subsets of consecutive tower
levels is itself a homomorphism-embedding. This is a key
ingredient for composing the projection chain from a small
top-level substructure to a cycle-free ancestor.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Restricting a homomorphism-embedding to a closed
substructure and its closed image again gives a
homomorphism-embedding. The preservation data comes from
the *ambient* exact embedding-on-irreducibles condition;
the nested induced structure is identified with a genuine
irreducible closed substructure of the ambient source. -/
theorem inducedClosedImage_isHomomorphismEmbedding
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hF : IsHomomorphismEmbedding act f)
    (S : Set V) (hS : A.IsClosed S)
    (hImage : B.IsClosed (imageSet f.toFun S)) :
    IsHomomorphismEmbedding act
      (inducedClosedImage act f S hS hImage) := by
  intro T hT hIrr
  let U : Set V := Subtype.val '' T
  let hU : A.IsClosed U :=
    Structure.isClosed_image_subtype A S hS T hT
  have hIrrU : (A.induce U hU).IsIrreducible :=
    TreeLike.nested_induce_irreducible A S hS T hT hIrr
  have hf := hF U hU hIrrU
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    apply Subtype.ext
    apply hf.1
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩
    · exact congrArg Subtype.val hab
  · intro n R xs hxs
    have hUxs : ∀ i, (Subtype.val ∘ xs) i ∈ U := by
      intro i
      exact ⟨xs i, hxs i, rfl⟩
    have hRel := hf.2.1 R (Subtype.val ∘ xs) hUxs
    change B.rel (act.onRel f.lang R) (f.toFun ∘ (Subtype.val ∘ xs)) ↔
      A.rel R (Subtype.val ∘ xs)
    exact hRel
  · intro n F xs hxs
    have hUxs : ∀ i, (Subtype.val ∘ xs) i ∈ U := by
      intro i
      exact ⟨xs i, hxs i, rfl⟩
    have hExact := hf.2.2 F (Subtype.val ∘ xs) hUxs
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzA : z.1 ∈ A.func F (Subtype.val ∘ xs) := hz
      have hzB : f z.1 ∈
          B.func (act.onFunc f.lang F)
            (f.toFun ∘ (Subtype.val ∘ xs)) := by
        rw [← hExact]
        exact ⟨z.1, hzA, rfl⟩
      have hzy' : f z.1 = y.1 := congrArg Subtype.val hzy
      rw [hzy'] at hzB
      change y.1 ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ (Subtype.val ∘ xs))
      exact hzB
    · intro hy
      have hyB : y.1 ∈
          B.func (act.onFunc f.lang F)
            (f.toFun ∘ (Subtype.val ∘ xs)) := by
        change y.1 ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ (Subtype.val ∘ xs)) at hy
        exact hy
      rw [← hExact] at hyB
      obtain ⟨z, hz, hzy⟩ := hyB
      have hzS : z ∈ S := hS F (Subtype.val ∘ xs)
        (fun i => (xs i).2) hz
      refine ⟨⟨z, hzS⟩, ?_, ?_⟩
      · exact hz
      · apply Subtype.ext
        exact hzy

end Homomorphism
end Structure

namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

/-- A projection between **actual closed subsets** of
consecutive stages of the sparsening tower is a
homomorphism-embedding, i.e. is an exact embedding on each
irreducible substructure of its induced domain. -/
theorem ClosedStageSubset.projectHom_isHomomorphismEmbedding
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.next act A E hfix hcomplete s)) :
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (ClosedStageSubset.projectHom act A E hfix hcomplete s T) := by
  letI : Finite s.Carrier := s.finiteCarrier
  exact Structure.Homomorphism.inducedClosedImage_isHomomorphismEmbedding
    act
    (FaithfulSparseningStage.nextProjection act A E hfix hcomplete s)
    (FaithfulSparseningStage.nextProjection_isHomomorphismEmbedding
      act A E hfix hcomplete s)
    T.support T.closed
    (ClosedStageSubset.project act A E hfix hcomplete s T).closed

end TreeLike
end AllThoseEPPA
