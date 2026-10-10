import AllThoseEPPA.TreeLikeFreeCutBaseMapIdentities

/-!
# Factorization of exact Γ-embeddings as an equality of embeddings

The existing `Embedding.factorThrough` construct is an
*exact Γ-embedding* and satisfies a pointwise equality:
if g:C↪B has image inside j:A↪B, then
j (factorThrough j g c) = g c.

For the recursive construction of a tree amalgamation
from full copies of A, the gluing *interface maps* must be
literally the composites `α.comp δ`, not just equal on
their vertex maps. This file strengthens the pointwise
factorization to the **equality of entire Γ-embeddings**,
including the language-permutation component.

The proof uses ordinary group cancellation for language
components; exact relation/function interpretation is
already supplied by the existing `factorThrough` embedding.
The remaining fields are proof-irrelevant.
-/

namespace AllThoseEPPA
namespace Structure
namespace Embedding

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x} {X : Type y}

/-- Exact Γ-structure embeddings between fixed structures
are equal when both their language components and underlying
vertex maps are equal. Preservation proofs are propositions,
hence proof irrelevant. -/
theorem ext_of_lang_toFun
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f g : Embedding act A B)
    (hLang : f.lang = g.lang)
    (hToFun : f.toFun = g.toFun) :
    f = g := by
  cases f with
  | mk lf vf ifl hrel hfunc =>
    cases g with
    | mk lg vg ig hrelg hfuncg =>
      cases hLang
      cases hToFun
      rfl

/-- The factorized Γ-embedding is an **exact two-sided
factorization**, as an equality of structure embeddings,
not merely equality of pointwise images or homomorphisms. -/
theorem comp_factorThrough
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    {C : Structure L X}
    (j : Embedding act A B)
    (g : Embedding act C B)
    (hRange : ∀ c : X, ∃ a : V, j a = g c) :
    j.comp (j.factorThrough act g hRange) = g := by
  apply ext_of_lang_toFun act
  · change j.lang * (j.lang⁻¹ * g.lang) = g.lang
    simp [mul_assoc]
  · funext c
    exact factorThrough_apply_spec act j g hRange c

end Embedding
end Structure
end AllThoseEPPA
