import AllThoseEPPA.StrongCompletionPushforwardLocalExact

/-!
# Exact criterion for a quotient map to be a homomorphism-embedding

Suppose f:A→B is a Γ-homomorphism-embedding and factors on
vertices as f=g∘q. Give U (the codomain of q) its canonical
existentially pushed structure.

Local injectivity and reflection of relation tuples are already
automatic. The remaining exactness requirement concerns function
fibres: if two tuples have the same q-image, then outputs with the
same f-image must have the same q-image.

This module proves this compatibility implies the WHOLE
homomorphism-embedding condition for q, including set-valued
functions of arbitrary arity. The compatibility itself is an
explicit premise, not an axiom; proving it for the special
one-point-closure collapse is a separate next task.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {U : Type x} {W : Type y}

/-- Compatibility of q with function outputs: no additional
function-fibre identifications are created by the pushforward
beyond those already witnessed by q itself. -/
def HasFunctionFibreCompatibility
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (q : V → U) : Prop :=
  ∀ {n : ℕ} (F : L.FuncSymbol n)
    (xs ys : Fin n → V),
    q ∘ xs = q ∘ ys →
    ∀ (a : V), a ∈ A.func F xs →
    ∀ (b : V), b ∈ A.func F ys →
    f a = f b → q a = q b

/-- The canonical quotient homomorphism becomes a full
homomorphism-embedding once its function fibres are compatible
with the original f-fibres. All other local exactness follows
from the original homomorphism-embedding f. -/
theorem toPushforward_isHomomorphismEmbedding_of_compatibility
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (hCompat : HasFunctionFibreCompatibility act f q) :
    IsHomomorphismEmbedding act (toPushforward act A q) := by
  intro S hS hIrr
  have hLocalF := hf S hS hIrr
  refine ⟨?_, ?_, ?_⟩
  · exact f.factor_injOn_of_homomorphismEmbedding
      act hf q g hFactor S hS hIrr
  · intro n R xs hxs
    change (A.pushforwardAlong q).rel (act.onRel (1 : Γ) R)
      (q ∘ xs) ↔ A.rel R xs
    rw [act.onRel_one]
    exact f.factor_pushforward_relation_exact_on_irreducible
      act hf q g hFactor S hS hIrr R xs hxs
  · intro n F xs hxs
    change imageSet q (A.func F xs) =
      (A.pushforwardAlong q).func (act.onFunc (1 : Γ) F)
        (q ∘ xs)
    rw [act.onFunc_one]
    apply Set.Subset.antisymm
    · intro z hz
      exact ⟨xs, rfl, hz⟩
    · intro z hz
      change (∃ ys : Fin n → V,
        q ∘ ys = q ∘ xs ∧ z ∈ imageSet q (A.func F ys)) at hz
      obtain ⟨ys, hys, ⟨b, hb, hqb⟩⟩ := hz
      have hTuple : f.toFun ∘ ys = f.toFun ∘ xs := by
        calc
          f.toFun ∘ ys = (g ∘ q) ∘ ys := by rw [hFactor]
          _ = g ∘ (q ∘ ys) := by funext i; rfl
          _ = g ∘ (q ∘ xs) := by rw [hys]
          _ = (g ∘ q) ∘ xs := by funext i; rfl
          _ = f.toFun ∘ xs := by rw [hFactor]
      have hfMem :
          f b ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ ys) :=
        f.map_func F ys ⟨b, hb, rfl⟩
      have hfMemXs :
          f b ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ xs) := by
        simpa only [hTuple] using hfMem
      rw [← hLocalF.2.2 F xs hxs] at hfMemXs
      obtain ⟨a, ha, hfa⟩ := hfMemXs
      have hqa : q a = q b :=
        hCompat F xs ys hys.symm a ha b hb hfa
      exact ⟨a, ha, hqa.trans hqb⟩

end Homomorphism
end Structure
end AllThoseEPPA
