import AllThoseEPPA.StrongCompletionPushforward

/-!
# Injectivity of descended homomorphisms on primitive images

Suppose a Γ-homomorphism-embedding f:A→B factors on vertices
as f = g ∘ q. The second factor g may not be injective on
arbitrary substructures of the intermediate carrier U.

However, for every closed irreducible S⊆A, g IS injective
on the image q(S), even when q is globally noninjective.

In particular, this holds for the image of every one-point
closure and for the image of the closure of every realized
relation tuple. The latter is the local condition needed
for the relation-saturation construction toward Proposition
11.3; no assertion about all irreducibles of U is made here.

This module does not require finite carriers, unary
functions or a trivial Γ-language action.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {U : Type x} {W : Type y}

/-- If f=g∘q and f is a homomorphism-embedding, then
g is injective on the q-image of every irreducible
closed source piece. -/
theorem descended_injOn_image_irreducible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (S : Set V) (hS : A.IsClosed S)
    (hIrr : (A.induce S hS).IsIrreducible) :
    Set.InjOn g (imageSet q S) := by
  intro u hu v hv huv
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hv
  have hfEq : f a = f b := by
    calc
      f a = g (q a) := congrFun hFactor a
      _ = g (q b) := huv
      _ = f b := (congrFun hFactor b).symm
  exact congrArg q ((hf S hS hIrr).1 ha hb hfEq)

/-- Descended injectivity on the image of any one-point
source closure. -/
theorem descended_injOn_image_closureAt
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (a : V) :
    Set.InjOn g (imageSet q (A.closureAtSet a)) := by
  exact f.descended_injOn_image_irreducible act hf
    q g hFactor (A.closureAtSet a)
    (A.isClosed_closureSet {a})
    (A.closureAt_isIrreducible a)

/-- Descended injectivity on the image of any actual
relation-tuple closure. This is a primitive support
for all arities, not a graph-only edge argument. -/
theorem descended_injOn_image_relationClosure
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → V)
    (hRel : A.rel R xs) :
    Set.InjOn g
      (imageSet q (A.closureSet (Set.range xs))) := by
  exact f.descended_injOn_image_irreducible act hf
    q g hFactor
    (A.closureSet (Set.range xs))
    (A.isClosed_closureSet (Set.range xs))
    (A.relationTupleClosure_isIrreducible R xs hRel)

end Homomorphism
end Structure
end AllThoseEPPA
