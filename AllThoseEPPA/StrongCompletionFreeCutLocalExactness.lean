import AllThoseEPPA.Irreducible
import AllThoseEPPA.TreeLikeHomEmbComposition

/-!
# Transporting local exactness across genuine free cuts

Suppose A has a free decomposition into two closed sides.
A Γ-homomorphism k:A→H may be obtained by gluing
two existing Γ-homomorphism-embeddings l,r:A→H, agreeing
with l on the left side and r on the right.

Although k is generally NOT a globally exact structure
embedding, it is a homomorphism-embedding: every closed
irreducible substructure of A lies inside one of the two
sides, and k has precisely the locally exact values and
Γ-language component of that side's map there.

The first lemma is independent of free cuts: local exactness
on a closed S depends only on the Γ-language component and
the vertex-map values on S, because all function outputs on
tuples in S again belong to S.

This is the local-exactness interface needed to lift a
finite source across a strong amalgam of *two copies of its
completion*, even though the original completion need
not be a global exact embedding.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- An embedding-on-S certificate transfers between two
Γ-homomorphisms which have the same Γ-language component
and agree pointwise on the closed source S.

The function-value direction uses that all values of a
tuple from S belong to S. -/
theorem embeddingOn_of_agree_on_closed
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (k h : Homomorphism act A B)
    (S : Set V) (hS : A.IsClosed S)
    (hLang : k.lang = h.lang)
    (hAgree : ∀ x : V, x ∈ S → k x = h x)
    (hh : IsEmbeddingOn act h S) :
    IsEmbeddingOn act k S := by
  have hTuple : ∀ {n : ℕ} (xs : Fin n → V),
      (∀ i, xs i ∈ S) →
        k.toFun ∘ xs = h.toFun ∘ xs := by
    intro n xs hxs
    funext i
    exact hAgree (xs i) (hxs i)
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    apply hh.1 ha hb
    calc
      h a = k a := (hAgree a ha).symm
      _ = k b := hab
      _ = h b := hAgree b hb
  · intro n R xs hxs
    have ht : k.toFun ∘ xs = h.toFun ∘ xs :=
      hTuple xs hxs
    simpa only [hLang, ht] using hh.2.1 R xs hxs
  · intro n F xs hxs
    have ht : k.toFun ∘ xs = h.toFun ∘ xs :=
      hTuple xs hxs
    have hImage : imageSet k.toFun (A.func F xs) =
        imageSet h.toFun (A.func F xs) := by
      ext z
      constructor
      · rintro ⟨a, ha, hka⟩
        have haS : a ∈ S := hS F xs hxs ha
        refine ⟨a, ha, ?_⟩
        calc
          h a = k a := (hAgree a haS).symm
          _ = z := hka
      · rintro ⟨a, ha, hha⟩
        have haS : a ∈ S := hS F xs hxs ha
        refine ⟨a, ha, ?_⟩
        calc
          k a = h a := hAgree a haS
          _ = z := hha
    calc
      imageSet k.toFun (A.func F xs) =
          imageSet h.toFun (A.func F xs) := hImage
      _ = B.func (act.onFunc h.lang F) (h.toFun ∘ xs) :=
        hh.2.2 F xs hxs
      _ = B.func (act.onFunc k.lang F) (k.toFun ∘ xs) := by
        rw [hLang, ht]

/-- If a Γ-homomorphism agrees with a homomorphism-embedding
on each of the two closed sides of a free decomposition, it
is a homomorphism-embedding of the entire source.

No finiteness, unary-function, or trivial-action assumption
is used in this structural locality lemma. -/
theorem homomorphismEmbedding_of_freeCut_side_agreement
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (d : A.FreeDecomposition)
    (k l r : Homomorphism act A B)
    (hl : IsHomomorphismEmbedding act l)
    (hr : IsHomomorphismEmbedding act r)
    (hlang : k.lang = l.lang)
    (hrang : k.lang = r.lang)
    (hleft : ∀ x : V, x ∈ d.left → k x = l x)
    (hright : ∀ x : V, x ∈ d.right → k x = r x) :
    IsHomomorphismEmbedding act k := by
  intro S hS hIrr
  rcases A.irreducible_subset_one_side d S hS hIrr with hsL | hsR
  · exact embeddingOn_of_agree_on_closed act
      k l S hS hlang (fun x hx => hleft x (hsL hx))
      (hl S hS hIrr)
  · exact embeddingOn_of_agree_on_closed act
      k r S hS hrang (fun x hx => hright x (hsR hx))
      (hr S hS hIrr)

end Homomorphism
end Structure
end AllThoseEPPA
