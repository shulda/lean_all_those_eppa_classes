import AllThoseEPPA.StrongCompletionCollapseSideInjectivity
import AllThoseEPPA.StrongCompletionLocalExactFactorization
import AllThoseEPPA.StrongCompletionFreeCutSAP
import AllThoseEPPA.StrongCompletionKernelDefect
import Mathlib.Data.Fintype.EquivFin

/-!
# Proposition 11.3: ordinary completions upgrade to strong completions

This is the complete ordinary-to-strong completion argument
for hereditary finite strong-amalgamation classes in languages
with genuinely set-valued UNARY functions and Γ-permuted symbols.

The proof combines the independently checked mathematical steps:

* A finite noninjective homomorphism-embedding admits a
  minimum-closure-score collided pair (l,r).
* The pair has a genuine five-region free cut.
* Collapsing the matching closures factors f as p followed
  by h, with p surjective and noninjective and BOTH maps
  genuine Γ-homomorphism-embeddings, preserving Γ-language.
* The first factor p is injective on BOTH sides of the cut.
* If the second factor h is injective, f is injective on
  both sides, so hereditary SAP produces a strong completion.
* If h remains noninjective, induction on the kernel defect
  |A| - |f(A)| gives a strong completion of the intermediate
  quotient. Composing with p gives a strictly lower-defect
  completion of A, and a second induction step finishes.

Crucially, this is a well-founded induction over ALL finite
source structures and finite target completions, not a global
choice of a minimal counterexample across heterogeneous types.
No unproved minimality principle is assumed.

The target class need not consist of irreducible structures;
that is an additional manuscript hypothesis, not needed here.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

open Structure

/-- Strong induction on the deficiency of a fixed ordinary
K-completion. This is the complete constructive core of
manuscript Proposition 11.3.

The precise rank is |V| - |f(V)| rather than the number of
unordered collapsed pairs; both permit strict descent through
the same local factorization. -/
theorem strongCompletion_of_completion_rank
    (act : L.Action Γ)
    (K : HereditaryFiniteStrongAmalgamationClass act)
    (n : ℕ) :
    ∀ {V : Type v} [Fintype V]
      (A : Structure L V)
      {W : Type v} [Finite W]
      (B : Structure L W)
      (f : Homomorphism act A B),
      K.mem B →
      Homomorphism.IsHomomorphismEmbedding act f →
      StrongCompletionKernel.kernelDefect f.toFun = n →
      K.toAmalgamationClass.HasStrongCompletion A := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V hFinV A W hFinW B f hKB hf hRank
    by_cases hInjective : Function.Injective f.toFun
    · exact ⟨W, hFinW, B, hKB, f, hf, hInjective⟩
    · obtain ⟨l, r, hMin⟩ :=
        f.exists_minimalClosureCollision act hInjective
      have hne : l ≠ r := hMin.1
      have hlr : f l = f r := hMin.2.1
      have hL : ∀ z : V, z ∈ A.leftExclusive l r →
          l ∈ A.closureAtSet z := by
        intro z hz
        exact f.leftExclusive_generates_of_minimalCollision
          act hf hMin hz
      have hR : ∀ z : V, z ∈ A.rightExclusive l r →
          r ∈ A.closureAtSet z := by
        intro z hz
        exact f.rightExclusive_generates_of_minimalCollision
          act hf hMin hz
      let d : A.FreeDecomposition :=
        f.fiveRegionFreeDecomposition act hf hne hlr hL hR

      -- The finite local quotient and its descended vertex map.
      let Q : Type v := f.localCollapseCarrier act hf hlr
      let q : V → Q := f.localCollapseToCarrier act hf hlr
      let g : Q → W := f.localCollapseDescent act hf hlr
      have hFactor : f.toFun = g ∘ q :=
        f.localCollapseDescent_comp act hf hlr
      have hSurj : Function.Surjective q :=
        f.localCollapseToCarrier_surjective act hf hlr
      have hNoninjQ : ¬ Function.Injective q :=
        f.localCollapseToCarrier_not_injective act hf hne hlr
      have hFinQ : Finite Q :=
        f.localCollapseCarrier_finite act hf hlr
      letI : Finite Q := hFinQ
      letI : Fintype Q := Fintype.ofFinite Q

      have hWeak :
          ∀ {m : ℕ} (F : L.FuncSymbol m)
            (xs ys : Fin m → V),
            q ∘ xs = q ∘ ys →
            ∀ z : V, z ∈ A.func F xs →
            ∀ t : V, t ∈ A.func F ys →
              f z = f t → q z = q t :=
        f.localCollapseCarrier_weakFibreCompatible act hf hlr
      have hCompat : A.FunctionFibresCompatible q :=
        f.functionFibresCompatible_of_unary_weak
          act hf q g hFactor hWeak

      -- Both factors are fully faithful on irreducible closed
      -- pieces, not merely homomorphisms of the vertex sets.
      let D : Structure L Q :=
        safeRelationSaturation act A q B g f.lang
      let p : Homomorphism act A D :=
        f.toSafeRelationSaturation act hf q g hFactor hCompat
      let h : Homomorphism act D B :=
        f.fromSafeRelationSaturation act q g hFactor
      have hp : Homomorphism.IsHomomorphismEmbedding act p :=
        f.toSafeRelationSaturation_isHomomorphismEmbedding
          act hf q g hFactor hCompat
      have hh : Homomorphism.IsHomomorphismEmbedding act h :=
        f.fromSafeRelationSaturation_isHomomorphismEmbedding
          act hf q g hFactor hSurj hCompat

      -- The chosen quotient is injective on each separate
      -- free-cut side, although it is not injective on A.
      have hCollapseSides :
          Set.InjOn (f.collapseRightClosure act hf hlr) d.left ∧
          Set.InjOn (f.collapseRightClosure act hf hlr) d.right :=
        f.minimalClosureCollision_collapse_injOn_both_sides
          act hf hMin
      have hqLeft : Set.InjOn q d.left := by
        intro x hx y hy hxy
        apply hCollapseSides.1 hx hy
        exact congrArg Subtype.val hxy
      have hqRight : Set.InjOn q d.right := by
        intro x hx y hy hxy
        apply hCollapseSides.2 hx hy
        exact congrArg Subtype.val hxy

      by_cases hInjH : Function.Injective h.toFun
      · -- An injective second factor leaves only collisions
        -- between the two sides; hereditary SAP separates them.
        have hFInjLeft : Set.InjOn f.toFun d.left := by
          intro x hx y hy hxy
          apply hqLeft hx hy
          apply hInjH
          change g (q x) = g (q y)
          calc
            g (q x) = f x := (congrFun hFactor x).symm
            _ = f y := hxy
            _ = g (q y) := congrFun hFactor y
        have hFInjRight : Set.InjOn f.toFun d.right := by
          intro x hx y hy hxy
          apply hqRight hx hy
          apply hInjH
          change g (q x) = g (q y)
          calc
            g (q x) = f x := (congrFun hFactor x).symm
            _ = f y := hxy
            _ = g (q y) := congrFun hFactor y
        exact strongCompletion_of_freeCut_sidewise_injective
          act K A d B f hf hKB hFInjLeft hFInjRight
      · -- With another collision in h, D admits a strong
        -- completion by induction at strictly smaller rank.
        have hSmallerH :
            StrongCompletionKernel.kernelDefect h.toFun < n := by
          have hs :=
            StrongCompletionKernel.kernelDefect_second_lt_composite
              q g hSurj hNoninjQ
          rw [← hFactor] at hs
          change StrongCompletionKernel.kernelDefect g < n
          simpa only [hRank] using hs
        have hStrongD : K.toAmalgamationClass.HasStrongCompletion D :=
          ih (StrongCompletionKernel.kernelDefect h.toFun)
            hSmallerH D B h hKB hh rfl
        obtain ⟨Z, hZ, C, hKC, e, he, hEInj⟩ := hStrongD
        letI : Finite Z := hZ
        let k : Homomorphism act A C := e.comp p
        have hk : Homomorphism.IsHomomorphismEmbedding act k :=
          Homomorphism.comp_isHomomorphismEmbedding
            act e p he hp
        have hSmallerP :
            StrongCompletionKernel.kernelDefect q < n := by
          have hs :=
            StrongCompletionKernel.kernelDefect_first_lt_composite
              q g hSurj hInjH
          rw [← hFactor] at hs
          simpa only [hRank] using hs
        have hDefK :
            StrongCompletionKernel.kernelDefect k.toFun =
              StrongCompletionKernel.kernelDefect q := by
          change StrongCompletionKernel.kernelDefect
              (e.toFun ∘ q) =
                StrongCompletionKernel.kernelDefect q
          exact StrongCompletionKernel.kernelDefect_postcompose_injective
            q e.toFun hEInj
        have hSmallerK :
            StrongCompletionKernel.kernelDefect k.toFun < n := by
          rw [hDefK]
          exact hSmallerP
        exact ih (StrongCompletionKernel.kernelDefect k.toFun)
          hSmallerK A C k hKC hk rfl

/-- **Manuscript Proposition 11.3 (strong-completion upgrade)**.
In any hereditary finite Γ-strong-amalgamation class of
structures with set-valued UNARY functions, an ordinary
Γ-homomorphism-embedding completion can always be replaced
by an injective Γ-homomorphism-embedding completion.

No automorphism-preserving lift is assumed or asserted;
that notion is strictly stronger than strong completion.
The argument does not require K's members to be irreducible,
so it also applies to the exact manuscript scope. -/
theorem hereditaryStrongAmalgamation_completionsUpgrade
    (act : L.Action Γ)
    (K : HereditaryFiniteStrongAmalgamationClass act)
    {V : Type v} [Finite V]
    (A : Structure L V)
    (h : K.toAmalgamationClass.HasCompletion A) :
    K.toAmalgamationClass.HasStrongCompletion A := by
  classical
  obtain ⟨W, hFinW, B, hKB, f, hf⟩ := h
  letI : Finite W := hFinW
  letI : Fintype V := Fintype.ofFinite V
  exact strongCompletion_of_completion_rank
    act K (StrongCompletionKernel.kernelDefect f.toFun)
    A B f hKB hf rfl

/-- The equivalence form stated by Proposition 11.3, including
the easy strong-to-ordinary direction. -/
theorem hereditaryStrongAmalgamation_completion_iff_strong
    (act : L.Action Γ)
    (K : HereditaryFiniteStrongAmalgamationClass act)
    {V : Type v} [Finite V]
    (A : Structure L V) :
    K.toAmalgamationClass.HasCompletion A ↔
      K.toAmalgamationClass.HasStrongCompletion A := by
  constructor
  · exact hereditaryStrongAmalgamation_completionsUpgrade act K A
  · exact K.toAmalgamationClass.hasCompletion_of_hasStrongCompletion A

end TreeLike
end AllThoseEPPA
