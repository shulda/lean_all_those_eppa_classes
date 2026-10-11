import AllThoseEPPA.StrongCompletionSafeQuotient
import AllThoseEPPA.StrongCompletionLocalQuotientCarrier
import AllThoseEPPA.StrongCompletionLocalCollapseUnaryFibres
import AllThoseEPPA.StrongCompletionUnaryFibreCongruence

/-!
# Two genuine homomorphism-embeddings factoring a local closure collision

Let A be a finite structure with set-valued unary functions,
and f:A→B a Γ-homomorphism-embedding. If f identifies two
distinct vertices a,b, the previously checked local collapse
identifies the matching points of Cl_A(b) and Cl_A(a).

The image of that collapse is a finite intermediate carrier Q.
We endow it with CONTROLLED RELATION SATURATION (rather than
the naive existential pushforward). The quotient map q:A→Q and
the descended map g:Q→B are both genuine Γ-homomorphism-
embeddings, and their composition agrees with f on all vertices
and its full Γ-language component. The first map q is
surjective and strictly noninjective.

The proof assembles four already isolated interfaces:
* the exact finite source collapse and its descent;
* unary output-fibre compatibility, upgraded to a congruence;
* homomorphism-embedding of the first map into safe saturation;
* homomorphism-embedding of the descended second map.

This is a factorization statement, NOT yet the ordinary-to-strong
completion result. The remaining final step uses a minimal bad
completion and the hereditary strong amalgamation class to
replace the last collision by two disjoint copies.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [Finite V] {W : Type x}

/-- The exact pointwise compatibility proved for the
unsubtyped collapse descends unchanged to the finite range
subtype, because equality of quotient vertices is just
equality of their underlying collapsed representatives. -/
theorem localCollapseCarrier_weakFibreCompatible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) :
    ∀ {n : ℕ} (F : L.FuncSymbol n)
      (xs ys : Fin n → V),
      f.localCollapseToCarrier act hf hab ∘ xs =
        f.localCollapseToCarrier act hf hab ∘ ys →
      ∀ (z : V), z ∈ A.func F xs →
      ∀ (t : V), t ∈ A.func F ys →
        f z = f t →
        f.localCollapseToCarrier act hf hab z =
          f.localCollapseToCarrier act hf hab t := by
  intro n F xs ys hTuples z hz t ht hzt
  have hPlain :
      f.collapseRightClosure act hf hab ∘ xs =
      f.collapseRightClosure act hf hab ∘ ys := by
    funext i
    exact congrArg Subtype.val (congrFun hTuples i)
  have hOut :
      f.collapseRightClosure act hf hab z =
      f.collapseRightClosure act hf hab t :=
    f.collapseRightClosure_function_fibre_compatible
      act hf hab F xs ys hPlain z hz t ht hzt
  exact Subtype.ext hOut

/-- The finite local closure collapse factors an arbitrary
noninjective Γ-homomorphism-embedding as two **genuine**
Γ-homomorphism-embeddings, the first a noninjective
surjection. The target B need not be finite.

This theorem does NOT assert that the intermediate
structure is a member of a given amalgamation class. -/
theorem exists_localCollapse_twoHomomorphismEmbeddings
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hne : a ≠ b) (hab : f a = f b) :
    ∃ (Q : Type w) (_ : Finite Q) (D : Structure L Q)
      (p : Homomorphism act A D)
      (h : Homomorphism act D B),
      IsHomomorphismEmbedding act p ∧
      IsHomomorphismEmbedding act h ∧
      Function.Surjective p.toFun ∧
      ¬ Function.Injective p.toFun ∧
      h.toFun ∘ p.toFun = f.toFun ∧
      h.lang * p.lang = f.lang := by
  classical
  let Q : Type w := f.localCollapseCarrier act hf hab
  let q : V → Q := f.localCollapseToCarrier act hf hab
  let g : Q → W := f.localCollapseDescent act hf hab
  have hFactor : f.toFun = g ∘ q :=
    f.localCollapseDescent_comp act hf hab
  have hSurj : Function.Surjective q :=
    f.localCollapseToCarrier_surjective act hf hab
  have hNoninj : ¬ Function.Injective q :=
    f.localCollapseToCarrier_not_injective act hf hne hab
  have hWeak :
      ∀ {n : ℕ} (F : L.FuncSymbol n)
        (xs ys : Fin n → V),
        q ∘ xs = q ∘ ys →
        ∀ (z : V), z ∈ A.func F xs →
        ∀ (t : V), t ∈ A.func F ys →
          f z = f t → q z = q t :=
    f.localCollapseCarrier_weakFibreCompatible act hf hab
  have hCompat : A.FunctionFibresCompatible q :=
    f.functionFibresCompatible_of_unary_weak
      act hf q g hFactor hWeak
  let D : Structure L Q :=
    safeRelationSaturation act A q B g f.lang
  let p : Homomorphism act A D :=
    f.toSafeRelationSaturation act hf q g hFactor hCompat
  let h : Homomorphism act D B :=
    f.fromSafeRelationSaturation act q g hFactor
  have hp : IsHomomorphismEmbedding act p :=
    f.toSafeRelationSaturation_isHomomorphismEmbedding
      act hf q g hFactor hCompat
  have hh : IsHomomorphismEmbedding act h :=
    f.fromSafeRelationSaturation_isHomomorphismEmbedding
      act hf q g hFactor hSurj hCompat
  have hFinite : Finite Q :=
    f.localCollapseCarrier_finite act hf hab
  refine ⟨Q, hFinite, D, p, h, hp, hh, hSurj,
    hNoninj, ?_, ?_⟩
  · exact hFactor.symm
  · change f.lang * 1 = f.lang
    simp

end Homomorphism
end Structure
end AllThoseEPPA
