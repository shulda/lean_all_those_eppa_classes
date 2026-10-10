import AllThoseEPPA.TreeLikeInfiniteCopiesSurjectiveInverse
import AllThoseEPPA.FaithfulInducedPartialIso
import AllThoseEPPA.EPPA

/-!
# Normalize an exact self-embedding of A by an ambient automorphism

For the base case of Lemma lem:infinitecopies, a leaf copy
C is Γ-isomorphic to A. An arbitrary other embedding
α:A↪C differs from the designated leaf isomorphism by
a Γ-self-embedding θ:A↪A. If θ is surjective (automatic
for finite A), the inverse θ⁻¹ is an exact Γ-embedding.

Regard θ⁻¹ as a full-source Γ-partial automorphism of A
and extend it to the ambient M. The resulting Γ-automorphism
σ normalizes the image of θ *pointwise*:
σ(a(θ x)) = a x, with the precise noncommutative
language equation σ.lang * a.lang * θ.lang = a.lang.

This lemma itself needs only the surjectivity of θ;
no finiteness or function-arity hypothesis is imposed.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- An ambient automorphism normalizes every surjective
Γ-self-embedding of A pointwise and in its language component,
provided all partial Γ-automorphisms of A extend along a:A↪M. -/
theorem exists_ambientNormalizer_selfEmbedding
    (act : L.Action Γ)
    {A : Structure L V} {M : Structure L W}
    (a : Structure.Embedding act A M)
    (hExt : ∀ p : Structure.PartialAutomorphism act A,
      ∃ g : Structure.Automorphism act M,
        Structure.ExtendsAlong act a p g)
    (θ : Structure.Embedding act A A)
    (hsurj : Function.Surjective θ.toFun) :
    ∃ σ : Structure.Automorphism act M,
      σ.lang * a.lang * θ.lang = a.lang ∧
      ∀ x : V, σ (a (θ x)) = a x := by
  classical
  let hUniv : A.IsClosed Set.univ := A.isClosed_univ
  let inv : Structure.Embedding act A A :=
    θ.inverseSurjective act hsurj
  let inc : Structure.Embedding act
      (A.induce Set.univ hUniv) A :=
    Structure.inclusion act A Set.univ hUniv
  let move : Structure.Embedding act
      (A.induce Set.univ hUniv) A :=
    inv.comp inc
  let p : Structure.PartialAutomorphism act A :=
    Faithful.partialAutomorphismOfInducedEmbedding
      act A Set.univ hUniv move
  have hpLang : p.lang = θ.lang⁻¹ := by
    change (θ.lang⁻¹ * 1) * 1 = θ.lang⁻¹
    simp
  obtain ⟨σ, hσ⟩ := hExt p
  refine ⟨σ, ?_, ?_⟩
  · calc
      σ.lang * a.lang * θ.lang =
          (a.lang * p.lang) * θ.lang := by rw [hσ.1]
      _ = a.lang * θ.lang⁻¹ * θ.lang := by rw [hpLang]
      _ = a.lang := by simp [mul_assoc]
  · intro x
    have hSource : θ x ∈ p.source := by
      change θ x ∈ Set.univ
      exact Set.mem_univ (θ x)
    have hpApply : p (θ x) = x := by
      have h := Faithful.partialAutomorphismOfInducedEmbedding_apply
        act A Set.univ hUniv move (Set.mem_univ (θ x))
      change p (θ x) = inv (θ x) at h
      have hInv :=
        congrArg (fun e : Structure.Embedding act A A => e x)
          (Structure.Embedding.inverseSurjective_comp act θ hsurj)
      change inv (θ x) = x at hInv
      exact h.trans hInv
    have h := hσ.2 (θ x) hSource
    rw [hpApply] at h
    exact h

end TreeLike
end AllThoseEPPA
