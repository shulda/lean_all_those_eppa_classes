import AllThoseEPPA.StrongCompletionMinimalClosurePair
import AllThoseEPPA.StrongCompletionFiveRegionFreeCut
import AllThoseEPPA.StrongCompletionLocalCollapse

/-!
# The local closure collapse is injective on BOTH sides of its free cut

For a collided pair l≠r with f(l)=f(r), choose the five-region
free cut from the two closure-generator properties. The local
collapse q identifies the matching one-point closures of r and l.

Although q is not injective on all of A, it is injective on
each of the two closed free-cut sides separately:
* The entire left region is fixed pointwise by q, since it
  avoids the right-exclusive closure.
* On the right region, a nontrivial q-collision would have
  one endpoint in the left one-point closure. Since the
  right region avoids L₁, this endpoint lies in the right
  one-point closure as well. Local injectivity of f on
  that closure then forbids the collision.

Consequently, if f=g∘q with g globally injective, f is
injective on each of those two sides, which is exactly the
input required by the strong amalgamation completion lemma.

The two generator properties are proved, rather than
assumed, when l,r minimize their one-point-closure score.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Any vertex of the five-region right side lying in
Cl(l) also lies in Cl(r). The right side cannot contain
a left-exclusive vertex. -/
theorem rightRegion_closureLeft_mem_closureRight
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    {z : V} (hz : z ∈ A.rightRegion l r)
    (hzLeft : z ∈ A.closureAtSet l) :
    z ∈ A.closureAtSet r := by
  by_contra hzRight
  have hzEx : z ∈ A.leftExclusive l r :=
    ⟨hzLeft, hzRight⟩
  rcases hz with hzC | hzRact
  · exact hzC.1 (Or.inl hzEx)
  · have hDisj : Disjoint (A.leftActive l r)
        (A.rightActive l r) :=
      f.activeSides_disjoint act hf hne hlr hL hR
    exact (Set.disjoint_left.mp hDisj) (Or.inl hzEx) hzRact

/-- The collapse is literally the identity on the
five-region LEFT side, and hence injective there. -/
theorem collapseRightClosure_injOn_leftRegion
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z) :
    Set.InjOn (f.collapseRightClosure act hf hlr)
      (A.leftRegion l r) := by
  have hDisj : Disjoint (A.leftActive l r)
      (A.rightActive l r) :=
    f.activeSides_disjoint act hf hne hlr hL hR
  have hFixed : ∀ z : V, z ∈ A.leftRegion l r →
      f.collapseRightClosure act hf hlr z = z := by
    intro z hz
    apply f.collapseRightClosure_eq_of_not_mem act hf hlr
    intro hzR
    rcases hz with hzC | hzAct
    · exact hzC.2 (Or.inl hzR)
    · exact (Set.disjoint_left.mp hDisj) hzAct (Or.inl hzR)
  intro x hx y hy hxy
  calc
    x = f.collapseRightClosure act hf hlr x := (hFixed x hx).symm
    _ = f.collapseRightClosure act hf hlr y := hxy
    _ = y := hFixed y hy

/-- A nontrivial collapse collision cannot occur WITHIN
the five-region RIGHT side either. The proof uses the
exact cross-closure shape of the local collapse kernel. -/
theorem collapseRightClosure_injOn_rightRegion
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z) :
    Set.InjOn (f.collapseRightClosure act hf hlr)
      (A.rightRegion l r) := by
  intro x hx y hy hxy
  by_cases hneXY : x = y
  · exact hneXY
  · rcases f.collapseRightClosure_collisions_only_cross
      act hf hlr hneXY hxy with
      ⟨hxR, hyL, hSame⟩ | ⟨hxL, hyR, hSame⟩
    · exact (f.injOn_closureAt act hf r) hxR
        (f.rightRegion_closureLeft_mem_closureRight
          act hf hne hlr hL hR hy hyL) hSame
    · exact (f.injOn_closureAt act hf r)
        (f.rightRegion_closureLeft_mem_closureRight
          act hf hne hlr hL hR hx hxL) hyR hSame

/-- For any finite minimum-score collided pair, the local
collapse is injective on each of the two closed sides of
the corresponding fully checked five-region free cut. -/
theorem minimalClosureCollision_collapse_injOn_both_sides
    [Finite V]
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V}
    (hMin : IsMinimalClosureCollision act f l r) :
    let d : A.FreeDecomposition :=
      f.fiveRegionFreeDecomposition act hf
        hMin.1 hMin.2.1
        (fun z hz => f.leftExclusive_generates_of_minimalCollision
          act hf hMin hz)
        (fun z hz => f.rightExclusive_generates_of_minimalCollision
          act hf hMin hz)
    Set.InjOn (f.collapseRightClosure act hf hMin.2.1) d.left ∧
      Set.InjOn (f.collapseRightClosure act hf hMin.2.1) d.right := by
  dsimp
  constructor
  · exact f.collapseRightClosure_injOn_leftRegion
      act hf hMin.1 hMin.2.1
      (fun z hz => f.leftExclusive_generates_of_minimalCollision
        act hf hMin hz)
      (fun z hz => f.rightExclusive_generates_of_minimalCollision
        act hf hMin hz)
  · exact f.collapseRightClosure_injOn_rightRegion
      act hf hMin.1 hMin.2.1
      (fun z hz => f.leftExclusive_generates_of_minimalCollision
        act hf hMin hz)
      (fun z hz => f.rightExclusive_generates_of_minimalCollision
        act hf hMin hz)

end Homomorphism
end Structure
end AllThoseEPPA
