import AllThoseEPPA.TreeLikeEmbeddingFactorComposition

/-!
# Inverses of surjective Γ-structure embeddings

For the base case of manuscript Lemma lem:infinitecopies,
a tree leaf is a full Γ-isomorphic copy C of A, presented
by an exact surjective embedding f:A↪C. The ambient
embedding a:A↪M must be transported to C using the
genuine inverse Γ-embedding C↪A, not just the inverse
vertex bijection: the Γ-language component must be
f.lang⁻¹ and all set-valued function fibres must agree.

The existing exact factorization theorem gives this
inverse with no finite-carrier or unarity hypothesis.
Here both inverse laws are proved *as equalities of
entire Γ-embeddings*.
-/

namespace AllThoseEPPA
namespace Structure
namespace Embedding

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Inverse of a surjective exact Γ-embedding, with vertex
inverse and Γ-language component f.lang⁻¹. -/
noncomputable def inverseSurjective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B)
    (hsurj : Function.Surjective f.toFun) :
    Embedding act B A :=
  f.factorThrough act (Embedding.id (act := act) B)
    (fun b => hsurj b)

@[simp] theorem inverseSurjective_lang
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B)
    (hsurj : Function.Surjective f.toFun) :
    (f.inverseSurjective act hsurj).lang = f.lang⁻¹ := by
  change f.lang⁻¹ * 1 = f.lang⁻¹
  simp

/-- f followed by its exact inverse is literally the identity
Γ-embedding of the target, not just the identity vertex map. -/
theorem comp_inverseSurjective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B)
    (hsurj : Function.Surjective f.toFun) :
    f.comp (f.inverseSurjective act hsurj) =
      Embedding.id (act := act) B := by
  exact comp_factorThrough act f (Embedding.id (act := act) B)
    (fun b => hsurj b)

/-- The other full Γ-embedding inverse law, including the
noncommutative Γ-language component. -/
theorem inverseSurjective_comp
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Embedding act A B)
    (hsurj : Function.Surjective f.toFun) :
    (f.inverseSurjective act hsurj).comp f =
      Embedding.id (act := act) A := by
  apply ext_of_lang_toFun act
  · change (f.lang⁻¹ * 1) * f.lang = 1
    simp [mul_assoc]
  · funext a
    have h :=
      congrArg
        (fun e : Embedding act B B => e (f a))
        (comp_inverseSurjective act f hsurj)
    exact f.injective h

end Embedding
end Structure
end AllThoseEPPA
