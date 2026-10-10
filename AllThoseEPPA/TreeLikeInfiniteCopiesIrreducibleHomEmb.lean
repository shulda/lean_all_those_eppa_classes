import AllThoseEPPA.TreeLikeInducedIrreducibles
import AllThoseEPPA.Irreducible

/-!
# A homomorphism-embedding out of an irreducible structure is an embedding

The next manuscript target after thm:maintree is Lemma lem:infinitecopies.
Its induction considers a homomorphism-embedding of a tree amalgamation
and then restricts the map to a full copy of irreducible A. On that
whole A-copy, a homomorphism-embedding must be an actual Γ-embedding:
injective, reflecting every relation and preserving exact set-valued
function fibres.

We first transfer whole-structure irreducibility to the structure
induced on the entire vertex set, and then specialize the global
embedding-on-each-irreducible definition to that subset.

There is no unary-function restriction, no finiteness assumption,
and no requirement that Γ acts trivially.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {V : Type w}

/-- An irreducible structure remains irreducible when represented as its
induced substructure on the full vertex set. -/
theorem irreducible_induce_univ
    (A : Structure L V) (hA : A.IsIrreducible) :
    (A.induce Set.univ (A.isClosed_univ)).IsIrreducible := by
  let e : V ≃ (Set.univ : Set V) :=
    { toFun := fun x => ⟨x, Set.mem_univ x⟩
      invFun := Subtype.val
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl }
  exact Structure.irreducible_of_equiv
    A (A.induce Set.univ (A.isClosed_univ)) e
    (by
      intro n R xs
      rfl)
    (by
      intro n F xs y
      rfl)
    hA

namespace Homomorphism

variable {Γ : Type v} [Group Γ] {W : Type x}

/-- On an irreducible entire domain, a homomorphism-embedding is a
genuine Γ-structure embedding, without any global-injectivity
hypothesis in its original definition. -/
noncomputable def toEmbedding_of_irreducible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hF : IsHomomorphismEmbedding act f)
    (hIrr : A.IsIrreducible) :
    Embedding act A B := by
  let S : Set V := Set.univ
  let hS : A.IsClosed S := A.isClosed_univ
  have hIrrUniv : (A.induce S hS).IsIrreducible :=
    irreducible_induce_univ A hIrr
  have hExact : IsEmbeddingOn act f S :=
    hF S hS hIrrUniv
  exact
    { lang := f.lang
      toFun := f.toFun
      injective := by
        intro a b hab
        exact hExact.1 (Set.mem_univ a) (Set.mem_univ b) hab
      map_rel_iff := by
        intro n R xs
        exact hExact.2.1 R xs (fun i => Set.mem_univ (xs i))
      map_func := by
        intro n F xs
        exact hExact.2.2 F xs (fun i => Set.mem_univ (xs i)) }

end Homomorphism
end Structure
end AllThoseEPPA
