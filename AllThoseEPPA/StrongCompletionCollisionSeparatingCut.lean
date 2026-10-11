import AllThoseEPPA.StrongCompletionMinimalClosurePair
import AllThoseEPPA.StrongCompletionFiveRegionFreeCut

/-!
# Every finite noninjective homomorphism-embedding admits
# a collision-separating free decomposition

This is a substantial nonconditional consequence of the
five-region construction of manuscript Proposition 11.3.

Choose a collided pair (l,r) minimizing the sum of the
sizes of their one-point closures. The preceding theorem
proves both generator properties L₁→l and R₁→r.
The earlier verified five-region argument then constructs
a genuine free decomposition d of A for which

  l ∈ d.left \\ d.right,   r ∈ d.right \\ d.left.

Thus every noninjective Γ-homomorphism-embedding from a
finite unary-function structure admits a free cut
SEPARATING AN ACTUAL IDENTIFIED PAIR.

No minimal-counterexample assumption, strong amalgamation
property, or extra axiom is required for this statement.
Obtaining strong completions from this cut still needs a
global argument to coordinate the two side completions
over their common induced substructure.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [Finite V] {W : Type x}

/-- Explicit collision-separating free cut.

The two selected source vertices have the same f-image,
but they lie in opposite *exclusive* regions of the
resulting free decomposition. In particular both sides
are proper and the chosen collision vanishes on either
of the two induced side substructures. -/
theorem exists_freeDecomposition_separating_collision
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (hNotInj : ¬ Function.Injective f.toFun) :
    ∃ (l r : V) (d : A.FreeDecomposition),
      l ≠ r ∧ f l = f r ∧
      l ∈ d.left ∧ l ∉ d.right ∧
      r ∈ d.right ∧ r ∉ d.left := by
  classical
  obtain ⟨l, r, hMin⟩ :=
    f.exists_minimalClosureCollision act hNotInj
  have hne : l ≠ r := hMin.1
  have hlr : f l = f r := hMin.2.1
  have hL :
      ∀ z : V, z ∈ A.leftExclusive l r →
        l ∈ A.closureAtSet z := by
    intro z hz
    exact f.leftExclusive_generates_of_minimalCollision
      act hf hMin hz
  have hR :
      ∀ z : V, z ∈ A.rightExclusive l r →
        r ∈ A.closureAtSet z := by
    intro z hz
    exact f.rightExclusive_generates_of_minimalCollision
      act hf hMin hz
  let d : A.FreeDecomposition :=
    f.fiveRegionFreeDecomposition act hf hne hlr hL hR
  have hlAct : l ∈ A.leftActive l r :=
    Or.inl (f.left_mem_leftExclusive_of_collision
      act hf hne hlr)
  have hrAct : r ∈ A.rightActive l r :=
    Or.inl (f.right_mem_rightExclusive_of_collision
      act hf hne hlr)
  have hDisjoint :
      Disjoint (A.leftActive l r) (A.rightActive l r) :=
    f.activeSides_disjoint act hf hne hlr hL hR
  refine ⟨l, r, d, hne, hlr, ?_, ?_, ?_, ?_⟩
  · change l ∈ A.leftRegion l r
    exact Or.inr hlAct
  · change l ∉ A.rightRegion l r
    intro h
    rcases h with hC | hRAct
    · exact hC.1 hlAct
    · exact (Set.disjoint_left.mp hDisjoint) hlAct hRAct
  · change r ∈ A.rightRegion l r
    exact Or.inr hrAct
  · change r ∉ A.leftRegion l r
    intro h
    rcases h with hC | hLAct
    · exact hC.2 hrAct
    · exact (Set.disjoint_left.mp hDisjoint) hLAct hrAct

end Homomorphism
end Structure
end AllThoseEPPA
