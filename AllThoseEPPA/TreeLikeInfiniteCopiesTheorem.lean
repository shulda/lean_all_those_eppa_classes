import AllThoseEPPA.TreeLikeInfiniteCopiesCompleteEReduct
import AllThoseEPPA.TreeLikeInfiniteCopiesCanonicalCompleteE

/-!
# Full literal manuscript Lemma lem:infinitecopies

The preceding theorem handled the canonical complete-E expansion
of an arbitrary old-language Γ-structure. The manuscript instead
allows ANY finite Γ-structure A⁺ in the expanded language, provided
its fresh E-relation is complete and loopless.

The checked canonicality lemma shows that
(A⁺)⁻.withCompleteFixedBinary = A⁺ *as literal structures*,
not only up to an isomorphism. We can therefore rewrite any
recursive TreeAmalgamation certificate for A⁺ to one for its
canonical complete expansion, apply the previously proved
mixed-language theorem, and rewrite the moreover assertion.

This loses no information about the Γ-symbol action,
function fibres, or individual embedded A-copies.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {V : Type v} {M : Type x}

/-- Exact manuscript infinitecopies theorem: from an arbitrary
finite E-complete expanded A, any literal full-A tree D
homomorphism-embeds after the E-reduct into an ambient
(possibly infinite) old-language Γ-structure M containing
A⁻ and extending all its partial automorphisms. Moreover
every expanded A-copy is normalized by some Γ-automorphism
of M, pointwise and in its language component. -/
theorem infiniteCopies_anyCompleteFreshE
    (act : L.Action Γ)
    (Aplus : Structure L.withFixedBinaryRel V) [Finite V]
    (hComplete : Aplus.EdgeComplete
      (Language.withFixedBinaryRel.freshE L))
    (N : Structure L M)
    (a : Structure.Embedding act Aplus.forgetFixedBinary N)
    (hExt : Structure.IsEPPAWitness act a)
    {U : Type v}
    (D : Structure L.withFixedBinaryRel U)
    (hTree : TreeAmalgamation act.withFixedBinaryRel Aplus D) :
    ∃ h : Structure.Homomorphism act D.forgetFixedBinary N,
      Structure.Homomorphism.IsHomomorphismEmbedding act h ∧
      ∀ β : Structure.Embedding act.withFixedBinaryRel Aplus D,
        ∃ σ : Structure.Automorphism act N,
          σ.lang * h.lang * (β.forgetFixedBinary act).lang = a.lang ∧
          ∀ x : V, σ (h (β x)) = a x := by
  have hCanonical :
      Aplus.forgetFixedBinary.withCompleteFixedBinary = Aplus :=
    Structure.withCompleteFixedBinary_eq_of_edgeComplete Aplus hComplete
  have hTreeCanonical : TreeAmalgamation act.withFixedBinaryRel
      Aplus.forgetFixedBinary.withCompleteFixedBinary D := by
    rw [hCanonical]
    exact hTree
  obtain ⟨h, hh, hNorm⟩ :=
    completeFreshETree_realizesIntoAmbient
      act Aplus.forgetFixedBinary N a hExt D hTreeCanonical
  refine ⟨h, hh, ?_⟩
  let P : Structure L.withFixedBinaryRel V → Prop := fun Q =>
    ∀ β : Structure.Embedding act.withFixedBinaryRel Q D,
      ∃ σ : Structure.Automorphism act N,
        σ.lang * h.lang * (β.forgetFixedBinary act).lang = a.lang ∧
        ∀ x : V, σ (h (β x)) = a x
  change P Aplus
  exact Eq.mp (congrArg P hCanonical) hNorm

end TreeLike
end AllThoseEPPA
