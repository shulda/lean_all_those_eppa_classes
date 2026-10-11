import Mathlib.Data.Set.Card
import Mathlib.Tactic
import AllThoseEPPA.StrongCompletionTwoClosureGeometry

/-!
# Minimal one-point-closure collision pairs

A useful simplification of the five-region construction in
manuscript Proposition 11.3 is to choose a collision
f(l)=f(r), l≠r, minimizing

       |Cl_A(l)| + |Cl_A(r)|.

Such a pair exists because natural numbers are well ordered.
If x lies in the exclusive left closure L₁=Cl(l)\\Cl(r),
the verified fibre-matching theorem supplies y in
R₁=Cl(r)\\Cl(l) with f(x)=f(y). Both Cl(x) and Cl(y)
are contained in Cl(l) and Cl(r), respectively. If x did
not generate l then Cl(x) would be a *proper* subset of
Cl(l), contradicting minimality of the sum. The right
side follows symmetrically.

Thus the two generator assumptions hL and hR of the
already-checked five-region free cut do not need to be
axioms or separately postulated: they follow from a
finite **local choice of the collided pair**.

This does not by itself settle Proposition 11.3: the
original proof also needs global minimization of the
number of f-collisions to make f injective on each
amalgamation side.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} [Finite V] {W : Type x}

/-- The closure-size score for a pair of source vertices. -/
def closurePairScore (A : Structure L V) (a b : V) : ℕ :=
  (A.closureAtSet a).ncard + (A.closureAtSet b).ncard

/-- A pair of distinct f-collided vertices minimizing the
sum of their one-point-closure cardinalities among ALL
collided pairs in the same finite source. -/
def IsMinimalClosureCollision
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B) (a b : V) : Prop :=
  a ≠ b ∧ f a = f b ∧
    ∀ x y : V, x ≠ y → f x = f y →
      closurePairScore A a b ≤ closurePairScore A x y

/-- Any noninjective map on a finite source has at least one
collision pair minimizing the closure-size score. -/
theorem exists_minimalClosureCollision
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hNotInj : ¬ Function.Injective f.toFun) :
    ∃ a b : V, IsMinimalClosureCollision act f a b := by
  classical
  have hPair : ∃ a b : V, a ≠ b ∧ f a = f b := by
    by_contra hn
    apply hNotInj
    intro a b h
    by_contra hne
    exact hn ⟨a, b, hne, h⟩
  let P : ℕ → Prop := fun n =>
    ∃ a b : V, a ≠ b ∧ f a = f b ∧ closurePairScore A a b = n
  have hExists : ∃ n, P n := by
    obtain ⟨a, b, hne, heq⟩ := hPair
    exact ⟨closurePairScore A a b, a, b, hne, heq, rfl⟩
  obtain ⟨a, b, hne, heq, hScore⟩ := Nat.find_spec hExists
  refine ⟨a, b, hne, heq, ?_⟩
  intro x y hxy hfxfy
  have hMin :
      Nat.find hExists ≤ closurePairScore A x y :=
    Nat.find_min' hExists ⟨x, y, hxy, hfxfy, rfl⟩
  simpa only [hScore] using hMin

/-- On a minimum-score collided pair, **every** point
of the exclusive left closure generates its chosen
left endpoint. No global minimal-completion assumption
is used. -/
theorem leftExclusive_generates_of_minimalCollision
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V}
    (hMin : IsMinimalClosureCollision act f l r)
    {z : V} (hz : z ∈ A.leftExclusive l r) :
    l ∈ A.closureAtSet z := by
  rcases hMin with ⟨hne, hfeq, hscore⟩
  by_contra hNot
  obtain ⟨y, ⟨hyRight, hfy⟩, _⟩ :=
    f.existsUnique_rightExclusive_fibreMate
      act hf hfeq z hz
  have hzy : z ≠ y := by
    intro h
    have hzRight : z ∈ A.closureAtSet r := by
      rw [h]
      exact hyRight.1
    exact hz.2 hzRight
  have hSubZ : A.closureAtSet z ⊆ A.closureAtSet l :=
    A.closureAtSet_subset_of_mem hz.1
  have hSubY : A.closureAtSet y ⊆ A.closureAtSet r :=
    A.closureAtSet_subset_of_mem hyRight.1
  have hStrictZ : A.closureAtSet z ⊂ A.closureAtSet l := by
    refine ⟨hSubZ, ?_⟩
    intro hReverse
    exact hNot (hReverse (A.mem_closureAtSet l))
  have hSmallerZ : (A.closureAtSet z).ncard <
      (A.closureAtSet l).ncard :=
    Set.ncard_lt_ncard hStrictZ
  have hSmallerY : (A.closureAtSet y).ncard ≤
      (A.closureAtSet r).ncard :=
    Set.ncard_le_ncard hSubY
  have hMinimalBound :
      closurePairScore A l r ≤ closurePairScore A z y :=
    hscore z y hzy hfy.symm
  unfold closurePairScore at hMinimalBound
  omega

/-- The minimum-score condition is invariant under
exchanging the two endpoints of the chosen collision. -/
theorem minimalClosureCollision_swap
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    {l r : V}
    (hMin : IsMinimalClosureCollision act f l r) :
    IsMinimalClosureCollision act f r l := by
  obtain ⟨hne, heq, hMinBound⟩ := hMin
  refine ⟨hne.symm, heq.symm, ?_⟩
  intro x y hxy hfxfy
  change closurePairScore A r l ≤ closurePairScore A x y
  calc
    closurePairScore A r l = closurePairScore A l r := by
      simp only [closurePairScore, add_comm]
    _ ≤ closurePairScore A x y := hMinBound x y hxy hfxfy

/-- Symmetric generator property for the exclusive right
closure, proved from the same minimal score. -/
theorem rightExclusive_generates_of_minimalCollision
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V}
    (hMin : IsMinimalClosureCollision act f l r)
    {z : V} (hz : z ∈ A.rightExclusive l r) :
    r ∈ A.closureAtSet z := by
  have hSwap := f.minimalClosureCollision_swap act hMin
  change z ∈ A.leftExclusive r l at hz
  exact f.leftExclusive_generates_of_minimalCollision
    act hf hSwap hz

end Homomorphism
end Structure
end AllThoseEPPA
