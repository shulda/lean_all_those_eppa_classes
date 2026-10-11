import AllThoseEPPA.StrongCompletionKernelDefect
import AllThoseEPPA.TreeLikeHomEmbComposition

/-!
# Minimal counterexamples admit no nontrivial surjective factorization

The published proof of Proposition 11.3 chooses a counterexample
whose completion identifies as few pairs as possible.

This module gives a structurally exact replacement based on the
kernel defect |A| - |f(A)|. A minimal non-strongly-completable
source A, together with a K-completion f:A→B, cannot factor as

           q            g
      A --------> A' --------> B

where q is a surjective homomorphism-embedding and BOTH q and g
are noninjective.

If A' has no strong K-completion, g witnesses a counterexample of
smaller defect. If A' does have a strong K-completion e:A'→C, then
e∘q is a completion of the original A of smaller defect.
Both cases contradict the precise minimality assumption.

This is the key *abstract* minimality argument. It still remains
to construct and audit the particular quotient q that identifies
only the two chosen one-point closures. No quotient existence
has been assumed here.
-/

namespace AllThoseEPPA
namespace TreeLike
namespace StrongCompletionKernel

universe u v w
variable {L : Language.{u}} {Γ : Type w} [Group Γ]
variable {act : L.Action Γ}

/-- Injective postcomposition does not change how many source
vertices were lost to kernel identifications. -/
theorem kernelDefect_postcompose_injective
    {X Y Z : Type v} [Fintype X]
    (q : X → Y) (e : Y → Z)
    (he : Function.Injective e) :
    kernelDefect (e ∘ q) = kernelDefect q := by
  have hImage : Set.range (e ∘ q) = e '' Set.range q := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨q a, ⟨a, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
  unfold kernelDefect
  rw [hImage, Set.ncard_image_of_injective _ he]

/-- A globally minimal counterexample to the ordinary-to-strong
completion theorem.

Global quantification over finite sources is necessary: after
surjective factorization the intermediate structure A' need
not be isomorphic to A. The definition requires NO strong
K-completion of A, a genuine K-completion f of A, and minimal
kernel defect among all such bad finite sources. -/
def IsMinimalBadCompletion
    (K : FiniteAmalgamationClass act)
    {V W : Type v} [Fintype V] [Finite W]
    (A : Structure L V) (B : Structure L W)
    (f : Structure.Homomorphism act A B) : Prop :=
  ¬ K.HasStrongCompletion A ∧
  K.mem B ∧
  Structure.Homomorphism.IsHomomorphismEmbedding act f ∧
  ∀ {X : Type v} [Fintype X] (D : Structure L X),
    ¬ K.HasStrongCompletion D →
    ∀ {Y : Type v} [Finite Y] (E : Structure L Y),
      K.mem E →
      ∀ (h : Structure.Homomorphism act D E),
        Structure.Homomorphism.IsHomomorphismEmbedding act h →
        kernelDefect f.toFun ≤ kernelDefect h.toFun

/-- **Minimal-factorization barrier.**
At a minimal bad completion, a surjective factorization through
homomorphism-embeddings cannot have BOTH a noninjective first
and a noninjective second map.

The proof handles the two possibilities for the intermediate
structure's strong-completability, and uses no assumptions
about a special class construction beyond its HasStrongCompletion
interface. -/
theorem minimalBadCompletion_no_two_noninjective_factors
    (K : FiniteAmalgamationClass act)
    {V U W : Type v} [Fintype V] [Fintype U] [Finite W]
    {A : Structure L V} {A' : Structure L U}
    {B : Structure L W}
    (f : Structure.Homomorphism act A B)
    (hMinimal : IsMinimalBadCompletion K A B f)
    (q : Structure.Homomorphism act A A')
    (hq : Structure.Homomorphism.IsHomomorphismEmbedding act q)
    (hSurj : Function.Surjective q.toFun)
    (g : Structure.Homomorphism act A' B)
    (hg : Structure.Homomorphism.IsHomomorphismEmbedding act g)
    (hFactor : f.toFun = g.toFun ∘ q.toFun)
    (hQNotInj : ¬ Function.Injective q.toFun)
    (hGNotInj : ¬ Function.Injective g.toFun) :
    False := by
  classical
  obtain ⟨hNoStrongA, hKB, _hf, hMin⟩ := hMinimal
  have hSecondSmaller :
      kernelDefect g.toFun < kernelDefect f.toFun := by
    have h := kernelDefect_second_lt_composite
      q.toFun g.toFun hSurj hQNotInj
    rw [← hFactor] at h
    exact h
  have hFirstSmaller :
      kernelDefect q.toFun < kernelDefect f.toFun := by
    have h := kernelDefect_first_lt_composite
      q.toFun g.toFun hSurj hGNotInj
    rw [← hFactor] at h
    exact h
  by_cases hStrong : K.HasStrongCompletion A'
  · obtain ⟨Z, hZ, C, hKC, e, he, hInj⟩ := hStrong
    letI : Finite Z := hZ
    let h : Structure.Homomorphism act A C := e.comp q
    have hh : Structure.Homomorphism.IsHomomorphismEmbedding act h :=
      Structure.Homomorphism.comp_isHomomorphismEmbedding
        act e q he hq
    have hDef : kernelDefect h.toFun = kernelDefect q.toFun :=
      kernelDefect_postcompose_injective q.toFun e.toFun hInj
    have hBound : kernelDefect f.toFun ≤ kernelDefect h.toFun :=
      hMin A hNoStrongA C hKC h hh
    omega
  · have hBound : kernelDefect f.toFun ≤ kernelDefect g.toFun :=
      hMin A' hStrong B hKB g hg
    omega

end StrongCompletionKernel
end TreeLike
end AllThoseEPPA
