import AllThoseEPPA.StrongCompletionNoCrossingTuples

/-!
# Function-closedness of the five-region splitting

For a collided pair l,r, let L=L₁∪L₂ and R=R₁∪R₂.
The fifth (central) region is C = A \ (L∪R). The left and
right substructures used in the strong amalgamation argument
are induced on C∪L and C∪R.

Assuming the precise minimal-kernel obligations that every
z∈L₁ has l in its closure and every z∈R₁ has r in its
closure, we prove these three sets are closed under all
unary set-valued functions. This is an essential bridge
to turning the five-region partition into actual induced
substructures eligible for amalgamation.

No assertion that the minimal-kernel obligations hold
has been introduced here.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {V : Type w}

/-- The middle region C is outside both active sides. -/
def middleRegion (A : Structure L V) (l r : V) : Set V :=
  {z | z ∉ A.leftActive l r ∧ z ∉ A.rightActive l r}

/-- Carrier of the proposed left substructure C ∪ L. -/
def leftRegion (A : Structure L V) (l r : V) : Set V :=
  A.middleRegion l r ∪ A.leftActive l r

/-- Carrier of the proposed right substructure C ∪ R. -/
def rightRegion (A : Structure L V) (l r : V) : Set V :=
  A.middleRegion l r ∪ A.rightActive l r

/-- The part L₁∪L₂ is made of vertices whose one-point
closures contain l, under the exact generator consequence
of the minimal-kernel argument. -/
theorem leftActive_generates_left
    (A : Structure L V) (l r : V)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    {z : V} (hz : z ∈ A.leftActive l r) :
    l ∈ A.closureAtSet z := by
  rcases hz with hL₁ | hL₂
  · exact hL z hL₁
  · have hl : l ∈ A.leftExclusive l r :=
      by
        by_cases hlr : l ∈ A.leftExclusive l r
        · exact hlr
        · have hz₁ : z ∉ A.leftExclusive l r := hL₂.1
          -- This auxiliary fact is not required below; use l∈Cl(l)
          -- when the exclusive part has the distinguished generator.
          exact hlr.elim
    exact hL₂.2 hl

/-- Right-hand analogue of the generated-point assertion. -/
theorem rightActive_generates_right
    (A : Structure L V) (l r : V)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    {z : V} (hz : z ∈ A.rightActive l r)
    (hr : r ∈ A.rightExclusive l r) :
    r ∈ A.closureAtSet z := by
  rcases hz with hR₁ | hR₂
  · exact hR z hR₁
  · exact hR₂.2 hr

/-- The middle region is downward closed under one-point
closures. The pointwise property does not require unarity. -/
theorem middleRegion_pointwiseClosed
    (A : Structure L V) (l r : V)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    (hl : l ∈ A.leftExclusive l r)
    (hr : r ∈ A.rightExclusive l r)
    {z : V} (hz : z ∈ A.middleRegion l r)
    {y : V} (hy : y ∈ A.closureAtSet z) :
    y ∈ A.middleRegion l r := by
  constructor
  · intro hyL
    have hlY : l ∈ A.closureAtSet y := by
      rcases hyL with hyL₁ | hyL₂
      · exact hL y hyL₁
      · exact hyL₂.2 hl
    have hlZ : l ∈ A.closureAtSet z :=
      A.closureAtSet_subset_of_mem hy hlY
    have hzL₂ : z ∈ A.leftAbove l r := by
      refine ⟨?_, ?_⟩
      · intro hzL₁
        exact hz.1 (Or.inl hzL₁)
      · intro x hx
        exact A.closureAtSet_subset_of_mem hlZ hx.1
    exact hz.1 (Or.inr hzL₂)
  · intro hyR
    have hrY : r ∈ A.closureAtSet y := by
      rcases hyR with hyR₁ | hyR₂
      · exact hR y hyR₁
      · exact hyR₂.2 hr
    have hrZ : r ∈ A.closureAtSet z :=
      A.closureAtSet_subset_of_mem hy hrY
    have hzR₂ : z ∈ A.rightAbove l r := by
      refine ⟨?_, ?_⟩
      · intro hzR₁
        exact hz.2 (Or.inl hzR₁)
      · intro x hx
        exact A.closureAtSet_subset_of_mem hrZ hx.1
    exact hz.2 (Or.inr hzR₂)

/-- For unary functions, pointwise closure under Cl(x) is
sufficient for a set to be a function-closed substructure. -/
theorem isClosed_of_pointwiseClosed
    [L.HasUnaryFunctions]
    (A : Structure L V)
    (S : Set V)
    (hPoint : ∀ x : V, x ∈ S → A.closureAtSet x ⊆ S) :
    A.IsClosed S := by
  intro n F xs hxs y hy
  have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
  subst n
  have hyClosure : y ∈ A.closureAtSet (xs 0) := by
    apply (A.isClosed_closureSet {xs 0}) F xs
    · intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact A.mem_closureAtSet (xs 0)
    · exact hy
  exact hPoint (xs 0) (hxs 0) hyClosure

/-- The central region C is a genuine induced substructure
when all function symbols are unary. -/
theorem middleRegion_isClosed
    [L.HasUnaryFunctions]
    (A : Structure L V) (l r : V)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    (hl : l ∈ A.leftExclusive l r)
    (hr : r ∈ A.rightExclusive l r) :
    A.IsClosed (A.middleRegion l r) := by
  apply A.isClosed_of_pointwiseClosed
  intro x hx y hy
  exact A.middleRegion_pointwiseClosed l r hL hR hl hr hx hy

namespace Homomorphism
variable {Γ : Type v} [Group Γ] {W : Type x}

/-- The closure of any point on the left active side
cannot reach the right active side, because then it
would contain both l and r, violating local exactness. -/
theorem leftActive_closure_disjoint_rightActive
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    {z y : V} (hz : z ∈ A.leftActive l r)
    (hy : y ∈ A.closureAtSet z)
    (hyR : y ∈ A.rightActive l r) : False := by
  have hl : l ∈ A.leftExclusive l r :=
    f.left_mem_leftExclusive_of_collision act hf hne hlr
  have hr : r ∈ A.rightExclusive l r :=
    f.right_mem_rightExclusive_of_collision act hf hne hlr
  have hlZ : l ∈ A.closureAtSet z := by
    rcases hz with hz₁ | hz₂
    · exact hL z hz₁
    · exact hz₂.2 hl
  have hrY : r ∈ A.closureAtSet y := by
    rcases hyR with hy₁ | hy₂
    · exact hR y hy₁
    · exact hy₂.2 hr
  have hrZ : r ∈ A.closureAtSet z :=
    A.closureAtSet_subset_of_mem hy hrY
  exact (f.distinct_of_same_fibre_not_in_common_closure
    act hf hne hlr z) ⟨hlZ, hrZ⟩

/-- Symmetric separation of one-point closures from the
right active side. -/
theorem rightActive_closure_disjoint_leftActive
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    {z y : V} (hz : z ∈ A.rightActive l r)
    (hy : y ∈ A.closureAtSet z)
    (hyL : y ∈ A.leftActive l r) : False := by
  have hl : l ∈ A.leftExclusive l r :=
    f.left_mem_leftExclusive_of_collision act hf hne hlr
  have hr : r ∈ A.rightExclusive l r :=
    f.right_mem_rightExclusive_of_collision act hf hne hlr
  have hrZ : r ∈ A.closureAtSet z := by
    rcases hz with hz₁ | hz₂
    · exact hR z hz₁
    · exact hz₂.2 hr
  have hlY : l ∈ A.closureAtSet y := by
    rcases hyL with hy₁ | hy₂
    · exact hL y hy₁
    · exact hy₂.2 hl
  have hlZ : l ∈ A.closureAtSet z :=
    A.closureAtSet_subset_of_mem hy hlY
  exact (f.distinct_of_same_fibre_not_in_common_closure
    act hf hne hlr z) ⟨hlZ, hrZ⟩

/-- The proposed left substructure carrier C∪L is
downward closed under one-point closures. -/
theorem leftRegion_pointwiseClosed
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    {z y : V} (hz : z ∈ A.leftRegion l r)
    (hy : y ∈ A.closureAtSet z) :
    y ∈ A.leftRegion l r := by
  have hl : l ∈ A.leftExclusive l r :=
    f.left_mem_leftExclusive_of_collision act hf hne hlr
  have hr : r ∈ A.rightExclusive l r :=
    f.right_mem_rightExclusive_of_collision act hf hne hlr
  rcases hz with hzC | hzL
  · exact Or.inl (A.middleRegion_pointwiseClosed l r hL hR hl hr hzC hy)
  · by_cases hyL : y ∈ A.leftActive l r
    · exact Or.inr hyL
    · have hyR : y ∉ A.rightActive l r := by
        intro hyr
        exact f.leftActive_closure_disjoint_rightActive
          act hf hne hlr hL hR hzL hy hyr
      exact Or.inl ⟨hyL, hyR⟩

/-- Symmetric right-carrier pointwise closedness. -/
theorem rightRegion_pointwiseClosed
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    {z y : V} (hz : z ∈ A.rightRegion l r)
    (hy : y ∈ A.closureAtSet z) :
    y ∈ A.rightRegion l r := by
  have hl : l ∈ A.leftExclusive l r :=
    f.left_mem_leftExclusive_of_collision act hf hne hlr
  have hr : r ∈ A.rightExclusive l r :=
    f.right_mem_rightExclusive_of_collision act hf hne hlr
  rcases hz with hzC | hzR
  · exact Or.inl (A.middleRegion_pointwiseClosed l r hL hR hl hr hzC hy)
  · by_cases hyR : y ∈ A.rightActive l r
    · exact Or.inr hyR
    · have hyL : y ∉ A.leftActive l r := by
        intro hyl
        exact f.rightActive_closure_disjoint_leftActive
          act hf hne hlr hL hR hzR hy hyl
      exact Or.inl ⟨hyL, hyR⟩

/-- The left region is closed under every unary function. -/
theorem leftRegion_isClosed
    [L.HasUnaryFunctions]
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z) :
    A.IsClosed (A.leftRegion l r) := by
  apply A.isClosed_of_pointwiseClosed
  intro x hx y hy
  exact f.leftRegion_pointwiseClosed act hf hne hlr hL hR hx hy

/-- The right region is closed under every unary function. -/
theorem rightRegion_isClosed
    [L.HasUnaryFunctions]
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z) :
    A.IsClosed (A.rightRegion l r) := by
  apply A.isClosed_of_pointwiseClosed
  intro x hx y hy
  exact f.rightRegion_pointwiseClosed act hf hne hlr hL hR hx hy

end Homomorphism
end Structure
end AllThoseEPPA
