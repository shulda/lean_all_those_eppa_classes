import AllThoseEPPA.TreeLikeTowerProjectionHomEmb
import AllThoseEPPA.TreeLikeIrreducibilityTransport

/-!
# Irreducible closed images of homomorphism-embeddings

A `Homomorphism.IsHomomorphismEmbedding` is exactly an
embedding on every irreducible closed induced substructure,
not necessarily on its entire source. To compose such maps,
we must know that the image of an irreducible closed
substructure is again **closed and irreducible**.

For a single closed irreducible source S, the
`IsEmbeddingOn` hypothesis provides exact preservation
of relation predicates and *equality of all set-valued
function fibres* on tuples from S. This makes the image
of S function-closed and produces a surjective Γ-embedding
from A induced on S onto B induced on f(S).

The previously checked Γ-isomorphism transport theorem
then proves the image irreducible. No assumption that f is
globally injective and no unary-function restriction is used.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- An exact embedding-on-closed-subset condition forces
the direct image of that subset to be function-closed,
even if the ambient homomorphism is noninjective elsewhere. -/
theorem image_isClosed_of_embeddingOn
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (S : Set V) (hS : A.IsClosed S)
    (hEmbedding : IsEmbeddingOn act f S) :
    B.IsClosed (imageSet f.toFun S) := by
  classical
  intro n F xs hxs y hy
  have hPre : ∀ i, ∃ z : V, z ∈ S ∧ f z = xs i := by
    intro i
    exact hxs i
  choose ys hysS hysEq using hPre
  have hTuple : f.toFun ∘ ys = xs := by
    funext i
    exact hysEq i
  let F₀ : L.FuncSymbol n := act.onFunc f.lang⁻¹ F
  have hF : act.onFunc f.lang F₀ = F := by
    simp [F₀, ← act.onFunc_mul]
  have hExact : imageSet f.toFun (A.func F₀ ys) = B.func F xs := by
    simpa only [hF, hTuple] using hEmbedding.2.2 F₀ ys hysS
  rw [← hExact] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  exact ⟨z, hS F₀ ys hysS hz, hzy⟩

/-- Every local exact embedding-on-a-closed-subset
induces a *surjective genuine Γ-embedding* onto the
structure induced by its closed image. -/
noncomputable def embeddingOnClosedImage
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (S : Set V) (hS : A.IsClosed S)
    (hEmbedding : IsEmbeddingOn act f S) :
    Embedding act (A.induce S hS)
      (B.induce (imageSet f.toFun S)
        (image_isClosed_of_embeddingOn act f S hS hEmbedding)) where
  lang := f.lang
  toFun := fun a => ⟨f a.1, ⟨a.1, a.2, rfl⟩⟩
  injective := by
    intro a b h
    apply Subtype.ext
    exact hEmbedding.1 a.2 b.2 (congrArg Subtype.val h)
  map_rel_iff := by
    intro n R xs
    have hLocal := hEmbedding.2.1 R (Subtype.val ∘ xs)
      (fun i => (xs i).2)
    simpa only [Structure.induce, Function.comp_def] using hLocal
  map_func := by
    intro n F xs
    have hLocal := hEmbedding.2.2 F (Subtype.val ∘ xs)
      (fun i => (xs i).2)
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzA : z.1 ∈ A.func F (Subtype.val ∘ xs) := hz
      have hzB : f z.1 ∈
          B.func (act.onFunc f.lang F)
            (f.toFun ∘ (Subtype.val ∘ xs)) := by
        rw [← hLocal]
        exact ⟨z.1, hzA, rfl⟩
      have hzy' : f z.1 = y.1 := congrArg Subtype.val hzy
      rw [hzy'] at hzB
      simpa only [Structure.induce, Function.comp_def] using hzB
    · intro hy
      have hyB : y.1 ∈
          B.func (act.onFunc f.lang F)
            (f.toFun ∘ (Subtype.val ∘ xs)) := by
        simpa only [Structure.induce, Function.comp_def] using hy
      rw [← hLocal] at hyB
      obtain ⟨z, hz, hzy⟩ := hyB
      have hzS : z ∈ S := hS F (Subtype.val ∘ xs)
        (fun i => (xs i).2) hz
      refine ⟨⟨z, hzS⟩, ?_, ?_⟩
      · exact hz
      · apply Subtype.ext
        exact hzy

/-- The local induced-range Γ-embedding is onto its
entire image by construction. -/
theorem embeddingOnClosedImage_surjective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (S : Set V) (hS : A.IsClosed S)
    (hEmbedding : IsEmbeddingOn act f S) :
    Function.Surjective
      (embeddingOnClosedImage act f S hS hEmbedding).toFun := by
  intro y
  obtain ⟨a, ha, hay⟩ := y.2
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  exact hay

/-- **Irreducibility of the actual projected image.**
If a closed source substructure is irreducible and
the homomorphism embeds it exactly, its induced closed
image is irreducible even if other vertices are
identified elsewhere by the ambient homomorphism. -/
theorem image_isIrreducible_of_embeddingOn
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (S : Set V) (hS : A.IsClosed S)
    (hEmbedding : IsEmbeddingOn act f S)
    (hIrr : (A.induce S hS).IsIrreducible) :
    (B.induce (imageSet f.toFun S)
      (image_isClosed_of_embeddingOn act f S hS hEmbedding)).IsIrreducible := by
  exact Structure.Embedding.irreducible_of_surjective act
    (embeddingOnClosedImage act f S hS hEmbedding)
    (embeddingOnClosedImage_surjective act f S hS hEmbedding)
    hIrr

end Homomorphism
end Structure
end AllThoseEPPA
