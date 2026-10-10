import Mathlib.Data.Fintype.Card
import AllThoseEPPA.TreeLikeFullAAmalgamation
import AllThoseEPPA.TreeLikeInfiniteCopiesSelfNormalizer
import AllThoseEPPA.TreeLikeInfiniteCopiesConjugatedGlue
import AllThoseEPPA.TreeLikeInfiniteCopiesNormalizationTransport
import AllThoseEPPA.TreeLikeInfiniteCopiesGeneralGluedHomEmb
import AllThoseEPPA.TreeLikeInfiniteCopiesEveryCopySide

/-!
# Tree amalgamations of a finite irreducible A map into ambient M

This is the full (non-reduct) Γ-structure version of the
tree-induction underlying manuscript Lemma lem:infinitecopies.

Suppose A is finite and irreducible, a:A↪M is an exact
Γ-embedding, and every partial Γ-automorphism of A
extends along a to a Γ-automorphism of M. Every literal
recursive tree amalgamation D of full copies of A then
admits a Γ-homomorphism-embedding h:D→M.

The *strong induction invariant* controls EVERY embedded
full A-copy α:A↪D: some ambient Γ-automorphism σ
normalizes σ∘h∘α = a both pointwise and in language.
This is stronger than the manuscript's setwise claim and
is exactly what permits the noncommutative Γ-glue.

The leaf case uses the genuine inverse of the designated
surjective Γ-embedding A↪D and the ambient extension
of an automorphism of finite A. The glue case uses the
checked exact Γ-compatible homomorphism-embedding gluing
theorem; every other A-copy factors through one side,
whose normalization is transported through the ambient
conjugation of that side.

No unary-function restriction is used in this structural
induction: arbitrary set-valued function arities are handled
by the existing exact Γ-homomorphism-embedding interface.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x
variable {L : Language.{u}} {Γ : Type w} [Group Γ]
variable {V : Type v} {M : Type x}

/-- The strengthened ambient-realization induction predicate,
including normalization of *every* embedded copy of A. -/
def AmbientTreeRealization
    (act : L.Action Γ) (A : Structure L V)
    (N : Structure L M)
    (a : Structure.Embedding act A N)
    {U : Type v} (D : Structure L U) : Prop :=
  ∃ h : Structure.Homomorphism act D N,
    Structure.Homomorphism.IsHomomorphismEmbedding act h ∧
    ∀ β : Structure.Embedding act A D,
      ∃ σ : Structure.Automorphism act N,
        σ.lang * h.lang * β.lang = a.lang ∧
        ∀ x : V, σ (h (β x)) = a x

/-- Full Γ-tree ambient-realization induction, with an
exact homomorphism-embedding of D into M and normalization
of every embedded A-copy, including non-designated copies. -/
theorem TreeAmalgamation.realizeIntoAmbient
    (act : L.Action Γ)
    (A : Structure L V) [Finite V]
    (hIrr : A.IsIrreducible)
    (N : Structure L M)
    (a : Structure.Embedding act A N)
    (hExt : Structure.IsEPPAWitness act a)
    {U : Type v} {D : Structure L U}
    (hTree : TreeAmalgamation act A D) :
    AmbientTreeRealization act A N a D := by
  classical
  induction hTree with
  | copy C f hsurj =>
      let inv : Structure.Embedding act C A :=
        f.inverseSurjective act hsurj
      let e : Structure.Embedding act C N := a.comp inv
      let h : Structure.Homomorphism act C N := e.toHomomorphism
      have hh : Structure.Homomorphism.IsHomomorphismEmbedding act h := by
        intro S hS hSirr
        refine ⟨?_, ?_, ?_⟩
        · intro x hx y hy hxy
          exact e.injective hxy
        · intro n R xs hxs
          exact e.map_rel_iff R xs
        · intro n F xs hxs
          exact e.map_func F xs
      refine ⟨h, hh, ?_⟩
      intro β
      let θ : Structure.Embedding act A A := inv.comp β
      have hθSurj : Function.Surjective θ.toFun :=
        Finite.surjective_of_injective θ.injective
      obtain ⟨σ, hσLang, hσApply⟩ :=
        exists_ambientNormalizer_selfEmbedding act a hExt θ hθSurj
      refine ⟨σ, ?_, ?_⟩
      · change σ.lang * (a.lang * inv.lang) * β.lang = a.lang
        change σ.lang * a.lang * (inv.lang * β.lang) = a.lang at hσLang
        simpa only [mul_assoc] using hσLang
      · intro x
        exact hσApply x
  | glue C B₁ B₂ hTree₁ hTree₂ δ₁ δ₂ α₁ α₂ ih₁ ih₂ =>
      obtain ⟨h₁, hh₁, hNormalize₁⟩ := ih₁
      obtain ⟨h₂, hh₂, hNormalize₂⟩ := ih₂
      obtain ⟨σ₁, hσLang₁, hσApply₁⟩ := hNormalize₁ α₁
      obtain ⟨σ₂, hσLang₂, hσApply₂⟩ := hNormalize₂ α₂
      obtain ⟨τ₁, τ₂, l, r, hl, hr, hLang, hAgree,
          hLeftLang, hLeftApply, hRightLang, hRightApply⟩ :=
        exists_compatible_normalizedSideMaps_withConjugations
          act a hExt α₁ α₂ δ₁ δ₂ h₁ h₂
          hh₁ hh₂ σ₁ σ₂ hσLang₁ hσLang₂
          hσApply₁ hσApply₂
      let f : Structure.Embedding act C B₁ := α₁.comp δ₁
      let g : Structure.Embedding act C B₂ := α₂.comp δ₂
      let φ : Structure.Homomorphism act
          (generalAmalgamStructure act f g) N :=
        generalAmalgamGluedHomomorphism
          act f g l r hLang hAgree
      have hφ : Structure.Homomorphism.IsHomomorphismEmbedding act φ :=
        generalAmalgamGluedHomomorphism_isHomomorphismEmbedding
          act f g l r hLang hAgree hl hr
      refine ⟨φ, hφ, ?_⟩
      intro β
      rcases irreducibleCopy_factors_generalAmalgam_side
          act f g hIrr β with
        ⟨β₁, hβ₁⟩ | ⟨β₂, hβ₂⟩
      · obtain ⟨σ, hσLang, hσApply⟩ := hNormalize₁ β₁
        let j : Structure.Embedding act B₁
            (generalAmalgamStructure act f g) :=
          generalAmalgamLeftEmbedding act f g
        have hφLang : φ.lang * j.lang = τ₁.lang * h₁.lang := by
          change l.lang * 1 = τ₁.lang * h₁.lang
          simpa [hLeftLang]
        have hφApply : ∀ b, φ (j b) = τ₁ (h₁ b) := by
          intro b
          calc
            φ (j b) = l b := rfl
            _ = τ₁ (h₁ b) := hLeftApply b
        obtain ⟨σ', hNewLang, hNewApply⟩ :=
          normalizeCopy_through_side_and_ambientAutomorphism
            act a h₁ φ j τ₁ hφLang hφApply β₁ σ
            hσLang hσApply
        have hjβ : j.comp β₁ = β := hβ₁
        refine ⟨σ', ?_, ?_⟩
        · simpa only [hjβ] using hNewLang
        · intro x
          simpa only [hjβ] using hNewApply x
      · obtain ⟨σ, hσLang, hσApply⟩ := hNormalize₂ β₂
        let j : Structure.Embedding act B₂
            (generalAmalgamStructure act f g) :=
          generalAmalgamRightEmbedding act f g
        have hφLang : φ.lang * j.lang = τ₂.lang * h₂.lang := by
          change l.lang * j.lang = τ₂.lang * h₂.lang
          rw [show j.lang = f.lang * g.lang⁻¹ from
            generalAmalgamRightEmbedding_lang act f g]
          calc
            l.lang * (f.lang * g.lang⁻¹) =
                (l.lang * f.lang) * g.lang⁻¹ := by
                  simp [mul_assoc]
            _ = (r.lang * g.lang) * g.lang⁻¹ := by rw [hLang]
            _ = r.lang := by simp [mul_assoc]
            _ = τ₂.lang * h₂.lang := hRightLang
        have hφApply : ∀ b, φ (j b) = τ₂ (h₂ b) := by
          intro b
          calc
            φ (j b) = r b := by
              change gluedCarrierMap f.toFun g.toFun l.toFun r.toFun
                (amalgamRight f.toFun g.toFun b) = r b
              exact gluedCarrierMap_right f.toFun g.toFun
                g.injective l.toFun r.toFun hAgree b
            _ = τ₂ (h₂ b) := hRightApply b
        obtain ⟨σ', hNewLang, hNewApply⟩ :=
          normalizeCopy_through_side_and_ambientAutomorphism
            act a h₂ φ j τ₂ hφLang hφApply β₂ σ
            hσLang hσApply
        have hjβ : j.comp β₂ = β := hβ₂
        refine ⟨σ', ?_, ?_⟩
        · simpa only [hjβ] using hNewLang
        · intro x
          simpa only [hjβ] using hNewApply x

end TreeLike
end AllThoseEPPA
