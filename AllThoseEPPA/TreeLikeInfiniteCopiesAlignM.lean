import AllThoseEPPA.TreeLikeInfiniteCopiesInterfaceAuto
import AllThoseEPPA.EPPA

/-!
# Align two images of an interface using an ambient automorphism

The hypotheses of Lemma lem:infinitecopies provide a Γ-structure M
containing a copy of A and extending every partial automorphism
of A. Given two Γ-embeddings δ₁,δ₂ of the same interface into A,
the canonical interface partial automorphism therefore extends
to an actual Γ-automorphism of M.

The full Γ-language law of the extension is recorded: the
automorphism conjugates the language components of the two
interfaces relative to the chosen embedding of A into M.
This is the alignment step needed for the inductive glue.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {V : Type x} {W : Type y}

/-- Extend the canonical partial automorphism determined by
two embeddings of a common interface into a full automorphism
of M; this aligns the two interface images on every vertex
and gives the exact Γ-language-component equation.

The extension assumption is ordinary EPPA **in M relative to
the particular embedding of A**, and M need not be finite. -/
theorem exists_ambientAutomorphism_aligning_interface
    (act : L.Action Γ)
    {C : Structure L I} {A : Structure L V}
    {M : Structure L W}
    (a : Structure.Embedding act A M)
    (hExt : ∀ p : Structure.PartialAutomorphism act A,
      ∃ g : Structure.Automorphism act M,
        Structure.ExtendsAlong act a p g)
    (δ₁ δ₂ : Structure.Embedding act C A) :
    ∃ g : Structure.Automorphism act M,
      g.lang * a.lang =
        a.lang * (δ₂.lang * δ₁.lang⁻¹) ∧
      ∀ c : I, g (a (δ₁ c)) = a (δ₂ c) := by
  let p : Structure.PartialAutomorphism act A :=
    interfacePartialAutomorphism act δ₁ δ₂
  obtain ⟨g, hg⟩ := hExt p
  refine ⟨g, ?_, ?_⟩
  · simpa only [p, interfacePartialAutomorphism_lang]
      using hg.1
  · intro c
    have hc : δ₁ c ∈ p.source := by
      change δ₁ c ∈ Set.range δ₁.toFun
      exact ⟨c, rfl⟩
    have h := hg.2 (δ₁ c) hc
    have hp : p (δ₁ c) = δ₂ c :=
      interfacePartialAutomorphism_apply act δ₁ δ₂ c
    rw [hp] at h
    exact h

end TreeLike
end AllThoseEPPA
