import AllThoseEPPA.StrongCompletionSafeRelationSaturation
import AllThoseEPPA.StrongCompletionInducedPrimitivePairSupport
import AllThoseEPPA.StrongCompletionDescendedPrimitiveInjectivity
import AllThoseEPPA.StrongCompletionPushforwardFunctionFibres
import AllThoseEPPA.StrongCompletionPushforwardDescendedFunctions

/-!
# The descended map from a controlled relation saturation is a homomorphism-embedding

The C₅/ternary counterexample forbids the naive existential
pushforward: it can create irreducibles on which the descent
fails to reflect relations. Our controlled saturation instead
accepts a tuple precisely when its target tuple is realized
and the descended map is injective on the closure of the tuple.

For unary functions, primitive pair support shows this suffices:
any pair of vertices in an irreducible induced substructure
lies together in either a one-point closure or a realized
relation-tuple closure. The descent is injective on both.
For a one-point closure this follows from exact closure
transport along a function-fibre congruence and local
injectivity of the ORIGINAL homomorphism-embedding. For a
relation-tuple closure it is part of the saturation definition.

Thus the descended map is a genuine homomorphism-embedding,
including exact set-valued unary function fibres. We make
the function-fibre congruence assumption explicit; it is
separately proved for the local closure collapse in the
unary branch.

The proof has no finiteness assumptions, and Γ may act
nontrivially on the language.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {U : Type x} {W : Type y}

/-- One-point closures in the controlled saturation are
precisely the images of original one-point closures, once
the quotient function fibres satisfy the congruence law. -/
theorem safeSaturation_closureAt_eq_image
    (act : L.Action Γ)
    (A : Structure L V) (q : V → U)
    (hCompat : A.FunctionFibresCompatible q)
    (B : Structure L W) (g : U → W) (lang : Γ)
    (a : V) :
    (safeRelationSaturation act A q B g lang).closureAtSet (q a) =
      imageSet q (A.closureAtSet a) := by
  have h := A.pushforward_image_closureSet_eq_of_compatible
    act q hCompat {a}
  change imageSet q (A.closureSet {a}) =
    (A.pushforwardAlong q).closureSet (imageSet q {a}) at h
  have hSet : imageSet q {a} = ({q a} : Set U) := by
    ext z
    simp [imageSet]
  rw [hSet] at h
  change (A.pushforwardAlong q).closureSet {q a} =
    imageSet q (A.closureSet {a})
  exact h.symm

/-- On every closed irreducible part of a controlled
saturation, the descended map is injective.

This is the missing injectivity bridge: the quotient's
irreducibles need not be images of irreducibles in the
original structure, but each PAIR in one has a primitive
support where the descended map is injective. -/
theorem safeSaturation_descended_injOn_irreducible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (hSurj : Function.Surjective q)
    (hCompat : A.FunctionFibresCompatible q)
    (S : Set U)
    (hS : (safeRelationSaturation act A q B g f.lang).IsClosed S)
    (hIrr : ((safeRelationSaturation act A q B g f.lang).induce
      S hS).IsIrreducible) :
    Set.InjOn g S := by
  let D : Structure L U := safeRelationSaturation act A q B g f.lang
  intro u hu v hv huv
  obtain ⟨z, hzS, hzU, hzV⟩ |
      ⟨n, R, xs, hxsS, hRel, huCl, hvCl⟩ :=
    D.irreducible_induced_primitivePairWitness S hS hIrr hu hv
  · obtain ⟨a, ha⟩ := hSurj z
    have hClosure :
        D.closureAtSet z = imageSet q (A.closureAtSet a) := by
      rw [← ha]
      exact safeSaturation_closureAt_eq_image
        act A q hCompat B g f.lang a
    have hInj : Set.InjOn g
        (imageSet q (A.closureAtSet a)) :=
      f.descended_injOn_image_closureAt
        act hf q g hFactor a
    apply hInj
    · rw [← hClosure]
      exact hzU
    · rw [← hClosure]
      exact hzV
    · exact huv
  · have hInj : Set.InjOn g
        (D.closureSet (Set.range xs)) := by
      exact hRel.2
    exact hInj huCl hvCl huv

/-- The *second factor* in the controlled saturation is a
Γ-homomorphism-embedding, not merely a homomorphism.

Unlike the false naive quotient transfer, this theorem checks
injectivity on ALL irreducibles, all reflected relation tuples,
and exact equality of ALL unary set-valued function fibres. -/
theorem fromSafeRelationSaturation_isHomomorphismEmbedding
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (hSurj : Function.Surjective q)
    (hCompat : A.FunctionFibresCompatible q) :
    IsHomomorphismEmbedding act
      (fromSafeRelationSaturation act f q g hFactor) := by
  let D : Structure L U :=
    safeRelationSaturation act A q B g f.lang
  intro S hS hIrr
  have hInj : Set.InjOn g S :=
    f.safeSaturation_descended_injOn_irreducible
      act hf q g hFactor hSurj hCompat S hS hIrr
  refine ⟨hInj, ?_, ?_⟩
  · intro n R xs hxs
    have hSupport : Set.range xs ⊆ S := by
      rintro z ⟨i, rfl⟩
      exact hxs i
    have hCl : D.closureSet (Set.range xs) ⊆ S :=
      D.closureSet_minimal hS hSupport
    have hClInj : Set.InjOn g (D.closureSet (Set.range xs)) := by
      intro a ha b hb heq
      exact hInj (hCl ha) (hCl hb) heq
    exact (safeRelationSaturation_rel_iff act A q B
      g f.lang R xs hClInj).symm
  · intro n F xs hxs
    exact f.fromPushforward_unary_map_func_exact
      act hf q g hFactor hSurj F xs

end Homomorphism
end Structure
end AllThoseEPPA
