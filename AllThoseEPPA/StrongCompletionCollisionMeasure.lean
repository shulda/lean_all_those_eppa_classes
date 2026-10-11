import Mathlib.Data.Fintype.Card
import AllThoseEPPA.StrongCompletionClassAPI

/-!
# A finite measure of noninjectivity for Proposition 11.3

The manuscript's proof of Proposition 11.3 chooses a
homomorphism-embedding with a *minimal number of identified
distinct pairs*. We formalize a convenient directed version
of this measure. Counting ordered pairs instead of unordered
pairs multiplies the value by two and does not change the
minimization argument.

The measure is zero exactly when the function is injective;
postcomposition by an injective function leaves it unchanged.
It makes sense for an arbitrary codomain, even an infinite one.

This file does not assume the difficult kernel-reduction lemma,
nor does it claim Proposition 11.3. It isolates the termination
measure for that subsequent argument.
-/

namespace AllThoseEPPA
namespace TreeLike
namespace StrongCompletionKernel

universe u v w
variable {V : Type v} {W : Type w} [Fintype V]

/-- Ordered pairs of *different* source vertices identified
by the vertex map f. The target need not be finite. -/
noncomputable def collisionPairs (f : V → W) : Finset (V × V) := by
  classical
  exact Finset.univ.filter
    (fun p : V × V => p.1 ≠ p.2 ∧ f p.1 = f p.2)

/-- The number of directed kernel pairs of f. -/
noncomputable def collisionCount (f : V → W) : ℕ :=
  (collisionPairs f).card

/-- Kernel pair membership is exactly inequality of source
vertices together with equality of images. -/
@[simp] theorem mem_collisionPairs (f : V → W)
    (a b : V) :
    (a,b) ∈ collisionPairs f ↔ a ≠ b ∧ f a = f b := by
  classical
  simp [collisionPairs]

/-- The collision count vanishes precisely for injective
functions. No assumptions on the codomain. -/
theorem collisionCount_eq_zero_iff_injective
    (f : V → W) :
    collisionCount f = 0 ↔ Function.Injective f := by
  classical
  constructor
  · intro h a b hab
    have hEmpty : collisionPairs f = ∅ := by
      apply Finset.card_eq_zero.mp
      exact h
    by_contra hne
    have hMem : (a,b) ∈ collisionPairs f :=
      (mem_collisionPairs f a b).2 ⟨hne, hab⟩
    rw [hEmpty] at hMem
    simp at hMem
  · intro hinj
    have hEmpty : collisionPairs f = ∅ := by
      apply Finset.ext
      intro p
      constructor
      · intro hp
        rcases p with ⟨a,b⟩
        obtain ⟨hne,heq⟩ := (mem_collisionPairs f a b).1 hp
        exact False.elim (hne (hinj heq))
      · intro hp
        simp at hp
    change (collisionPairs f).card = 0
    rw [hEmpty]
    rfl

/-- Postcomposition with an injection neither creates nor
removes kernel collisions. -/
theorem collisionCount_postcompose_injective
    {X : Type u} (f : V → W) (g : W → X)
    (hg : Function.Injective g) :
    collisionCount (g ∘ f) = collisionCount f := by
  classical
  have hSets : collisionPairs (g ∘ f) = collisionPairs f := by
    ext p
    rcases p with ⟨a,b⟩
    rw [mem_collisionPairs, mem_collisionPairs]
    constructor
    · rintro ⟨hne, heq⟩
      exact ⟨hne, hg heq⟩
    · rintro ⟨hne, heq⟩
      exact ⟨hne, congrArg g heq⟩
  exact congrArg Finset.card hSets

end StrongCompletionKernel
end TreeLike
end AllThoseEPPA
