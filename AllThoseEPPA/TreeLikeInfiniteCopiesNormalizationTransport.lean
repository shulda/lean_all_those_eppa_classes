import AllThoseEPPA.Automorphism
import AllThoseEPPA.TreeLikeEmbeddingFactorComposition

/-!
# The normalization invariant survives an automorphism of M

For the "moreover" clause of manuscript Lemma lem:infinitecopies,
a homomorphism-embedding h:B→M carries *each* copy of A
into a copy that can be moved pointwise onto a fixed
embedded A⊆M by some Γ-automorphism of M.

At a gluing step, the map on one side is changed by an
ambient Γ-automorphism τ, and the source side is inserted
in the new amalgam by an exact Γ-embedding j:B↪D.
If φ:D→M satisfies the expected language and pointwise
restriction equations, an already normalized A-copy in B
remains normalizable when viewed inside D.

The new normalizer is σ∘τ⁻¹. Both the pointwise action
and noncommutative Γ-language component are proved exactly,
and the result works for arbitrary relational arities,
set-valued functions and infinite carriers.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y z
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {X : Type x} {Y : Type y}
variable {M : Type z}

/-- Transport pointwise Γ-normalization of an A-copy through
an exact side embedding followed by an ambient automorphism.
No homomorphism-embedding hypothesis is needed for this
*algebraic* transport step; it is supplied in the later glue. -/
theorem normalizeCopy_through_side_and_ambientAutomorphism
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L X}
    {D : Structure L Y} {N : Structure L M}
    (a : Structure.Embedding act A N)
    (h : Structure.Homomorphism act B N)
    (φ : Structure.Homomorphism act D N)
    (j : Structure.Embedding act B D)
    (τ : Structure.Automorphism act N)
    (hLang : φ.lang * j.lang = τ.lang * h.lang)
    (hApply : ∀ b : X, φ (j b) = τ (h b))
    (β : Structure.Embedding act A B)
    (σ : Structure.Automorphism act N)
    (hNormLang : σ.lang * h.lang * β.lang = a.lang)
    (hNormApply : ∀ x : V, σ (h (β x)) = a x) :
    ∃ σ' : Structure.Automorphism act N,
      σ'.lang * φ.lang * (j.comp β).lang = a.lang ∧
      ∀ x : V, σ' (φ ((j.comp β) x)) = a x := by
  classical
  refine ⟨σ.comp τ.symm, ?_, ?_⟩
  · change
      (σ.lang * τ.lang⁻¹) * φ.lang * (j.lang * β.lang) =
        a.lang
    calc
      (σ.lang * τ.lang⁻¹) * φ.lang * (j.lang * β.lang) =
          (σ.lang * τ.lang⁻¹) * (φ.lang * j.lang) * β.lang := by
            simp [mul_assoc]
      _ = (σ.lang * τ.lang⁻¹) * (τ.lang * h.lang) * β.lang := by
        rw [hLang]
      _ = σ.lang * h.lang * β.lang := by simp [mul_assoc]
      _ = a.lang := hNormLang
  · intro x
    change σ (τ.symm (φ (j (β x)))) = a x
    rw [hApply (β x)]
    rw [Structure.Automorphism.symm_apply_apply τ (h (β x))]
    exact hNormApply x

end TreeLike
end AllThoseEPPA
