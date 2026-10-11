import AllThoseEPPA.StrongCompletionPushforward

/-!
# Relation-exactness of any factor quotient of a homomorphism-embedding

Let f:A→B be a Γ-homomorphism-embedding and let its vertex map
factor as f=g∘q. Equip q's codomain with the existential
pushforward structure q₊A.

Then the quotient homomorphism q:A→q₊A is already:
* injective on every irreducible closed substructure of A;
* exact (preserves AND reflects) on all relation tuples
  supported by such a substructure.

The proof uses the local exactness of f, and does NOT use
unarity, global injectivity of f, surjectivity of q, or
anything about the source/target carrier sizes.

Thus the only missing local-embedding-on-source condition
for q is the exact equality of its set-valued function
fibres on irreducible closed pieces. For the local closure
collapse this is the key unary-function calculation.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {U : Type x} {W : Type y}

/-- Every factor q of f is locally injective wherever f
is known to be an exact embedding. -/
theorem factor_injOn_of_homomorphismEmbedding
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (S : Set V) (hS : A.IsClosed S)
    (hIrr : (A.induce S hS).IsIrreducible) :
    Set.InjOn q S := by
  intro a ha b hb hab
  apply (hf S hS hIrr).1 ha hb
  calc
    f a = g (q a) := congrFun hFactor a
    _ = g (q b) := by rw [hab]
    _ = f b := (congrFun hFactor b).symm

/-- The existentially pushed structure cannot introduce a
new relation tuple on any irreducible closed source piece:
such a tuple would be witnessed in A and so hold in B;
the original f reflects it back to the selected piece. -/
theorem factor_pushforward_relation_exact_on_irreducible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (S : Set V) (hS : A.IsClosed S)
    (hIrr : (A.induce S hS).IsIrreducible)
    {n : ℕ} (R : L.RelSymbol n)
    (xs : Fin n → V) (hxs : ∀ i, xs i ∈ S) :
    (A.pushforwardAlong q).rel R (q ∘ xs) ↔ A.rel R xs := by
  constructor
  · intro hrel
    change (∃ ys : Fin n → V,
      q ∘ ys = q ∘ xs ∧ A.rel R ys) at hrel
    obtain ⟨ys, hys, hyrel⟩ := hrel
    have hfRel :
        B.rel (act.onRel f.lang R) (f.toFun ∘ ys) :=
      f.map_rel R ys hyrel
    have hTuple : f.toFun ∘ ys = f.toFun ∘ xs := by
      calc
        f.toFun ∘ ys = (g ∘ q) ∘ ys := by rw [hFactor]
        _ = g ∘ (q ∘ ys) := by funext i; rfl
        _ = g ∘ (q ∘ xs) := by rw [hys]
        _ = (g ∘ q) ∘ xs := by funext i; rfl
        _ = f.toFun ∘ xs := by rw [hFactor]
    have hfRelXs :
        B.rel (act.onRel f.lang R) (f.toFun ∘ xs) := by
      simpa only [hTuple] using hfRel
    exact ((hf S hS hIrr).2.1 R xs hxs).mp hfRelXs
  · intro hrel
    exact ⟨xs, rfl, hrel⟩

end Homomorphism
end Structure
end AllThoseEPPA
