import AllThoseEPPA.StrongCompletionFiveRegionClosure

/-!
# An actual free cut from the five-region decomposition

After the minimal-kernel part of Proposition 11.3 has supplied
the two generator properties hL and hR, the regions

    left = C ∪ L₁ ∪ L₂,      right = C ∪ R₁ ∪ R₂

form not merely a covering of the vertex set: they are
closed induced substructures and form a genuine FREE
decomposition of A.

The relation-locality statement uses the earlier
no-crossing-tuple lemma, and function fibres on a mixed
tuple are automatically empty because all functions are
unary and the two sides jointly cover the vertex set.

The construction is conditional on hL and hR. It does NOT
establish those two minimal-kernel properties and hence
does not establish Proposition 11.3 by itself.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {V : Type w}
variable {Γ : Type v} [Group Γ] {W : Type x}

namespace Homomorphism

/-- The active left and right regions are disjoint.
Every one-point closure containing a point on both
sides would contain both identified generators. -/
theorem activeSides_disjoint
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z) :
    Disjoint (A.leftActive l r) (A.rightActive l r) := by
  apply Set.disjoint_left.mpr
  intro z hzL hzR
  have hl : l ∈ A.leftExclusive l r :=
    f.left_mem_leftExclusive_of_collision act hf hne hlr
  have hr : r ∈ A.rightExclusive l r :=
    f.right_mem_rightExclusive_of_collision act hf hne hlr
  have hlZ : l ∈ A.closureAtSet z :=
    A.leftActive_generates_left l r hL hl hzL
  have hrZ : r ∈ A.closureAtSet z :=
    A.rightActive_generates_right l r hR hzR hr
  exact (f.distinct_of_same_fibre_not_in_common_closure
    act hf hne hlr z) ⟨hlZ, hrZ⟩

/-- The two induced side carriers jointly cover all vertices. -/
theorem leftRegion_union_rightRegion
    (A : Structure L V) (l r : V) :
    A.leftRegion l r ∪ A.rightRegion l r = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  by_cases hzL : z ∈ A.leftActive l r
  · exact Or.inl (Or.inr hzL)
  · by_cases hzR : z ∈ A.rightActive l r
    · exact Or.inr (Or.inr hzR)
    · exact Or.inl (Or.inl ⟨hzL, hzR⟩)

/-- The precise interface of the two sides is C. -/
theorem leftRegion_inter_rightRegion
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z) :
    A.leftRegion l r ∩ A.rightRegion l r =
      A.middleRegion l r := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzL, hzR⟩
    rcases hzL with hzC | hzActL
    · exact hzC
    · rcases hzR with hzC | hzActR
      · exact hzC
      · exact False.elim
          ((Set.disjoint_left.mp
            (f.activeSides_disjoint act hf hne hlr hL hR))
              hzActL hzActR)
  · intro z hz
    exact ⟨Or.inl hz, Or.inl hz⟩

/-- Neither side is all of A: the opposite distinguished
generator belongs exclusively to the other active side. -/
theorem leftRegion_proper
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z) :
    A.leftRegion l r ≠ Set.univ := by
  intro h
  have hrEx : r ∈ A.rightExclusive l r :=
    f.right_mem_rightExclusive_of_collision act hf hne hlr
  have hrAct : r ∈ A.rightActive l r := Or.inl hrEx
  have hrLeft : r ∈ A.leftRegion l r := by
    rw [h]
    exact Set.mem_univ r
  rcases hrLeft with hrC | hrActL
  · exact hrC.2 hrAct
  · exact (Set.disjoint_left.mp
      (f.activeSides_disjoint act hf hne hlr hL hR)) hrActL hrAct

theorem rightRegion_proper
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z) :
    A.rightRegion l r ≠ Set.univ := by
  intro h
  have hlEx : l ∈ A.leftExclusive l r :=
    f.left_mem_leftExclusive_of_collision act hf hne hlr
  have hlAct : l ∈ A.leftActive l r := Or.inl hlEx
  have hlRight : l ∈ A.rightRegion l r := by
    rw [h]
    exact Set.mem_univ l
  rcases hlRight with hlC | hlActR
  · exact hlC.1 hlAct
  · exact (Set.disjoint_left.mp
      (f.activeSides_disjoint act hf hne hlr hL hR)) hlAct hlActR

/-- Every realized relation tuple is supported wholly on one
of the two sides. This is the relation-locality axiom of
the free-decomposition structure, for arbitrary arity. -/
theorem fiveRegion_relation_local
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → V)
    (hRel : A.rel R xs) :
    (∀ i, xs i ∈ A.leftRegion l r) ∨
      (∀ i, xs i ∈ A.rightRegion l r) := by
  classical
  by_contra h
  have hNotLeft : ¬ ∀ i, xs i ∈ A.leftRegion l r := by
    intro hleft
    exact h (Or.inl hleft)
  have hNotRight : ¬ ∀ i, xs i ∈ A.rightRegion l r := by
    intro hright
    exact h (Or.inr hright)
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hNotLeft
  obtain ⟨j, hj⟩ := Classical.not_forall.mp hNotRight
  have hiRight : xs i ∈ A.rightActive l r := by
    have hcover : xs i ∈ A.leftRegion l r ∪
        A.rightRegion l r := by
      rw [leftRegion_union_rightRegion A l r]
      exact Set.mem_univ _
    rcases hcover with hiLeft | hiRight
    · exact False.elim (hi hiLeft)
    · rcases hiRight with hiC | hiAct
      · exact False.elim (hi (Or.inl hiC))
      · exact hiAct
  have hjLeft : xs j ∈ A.leftActive l r := by
    have hcover : xs j ∈ A.leftRegion l r ∪
        A.rightRegion l r := by
      rw [leftRegion_union_rightRegion A l r]
      exact Set.mem_univ _
    rcases hcover with hjLeft | hjRight
    · rcases hjLeft with hjC | hjAct
      · exact False.elim (hj (Or.inl hjC))
      · exact hjAct
    · exact False.elim (hj hjRight)
  exact f.relationTuple_cannot_cross_active_sides
    act hf hne hlr hL hR R xs hRel ⟨j, i, hjLeft, hiRight⟩

/-- In a unary-function language, a tuple cannot fail to
lie entirely in at least one of two covering sides:
each input tuple consists of one vertex. -/
theorem fiveRegion_function_cross_empty
    (A : Structure L V) (l r : V)
    {n : ℕ} (F : L.FuncSymbol n)
    (xs : Fin n → V)
    (hCross : ¬ ((∀ i, xs i ∈ A.leftRegion l r) ∨
      (∀ i, xs i ∈ A.rightRegion l r))) :
    A.func F xs = ∅ := by
  have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
  subst n
  have hCover : xs 0 ∈ A.leftRegion l r ∪
      A.rightRegion l r := by
    rw [leftRegion_union_rightRegion A l r]
    exact Set.mem_univ _
  have hImpossible : False := by
    rcases hCover with hLeft | hRight
    · apply hCross (Or.inl ?_)
      intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact hLeft
    · apply hCross (Or.inr ?_)
      intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact hRight
  exact hImpossible.elim

/-- The five-region construction is a genuine free
decomposition, not just a partition of the vertex set.
Every field is checked against the set-valued Γ-structure
definitions; minimal-kernel obligations remain explicit. -/
noncomputable def fiveRegionFreeDecomposition
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {l r : V} (hne : l ≠ r) (hlr : f l = f r)
    (hL : ∀ z : V, z ∈ A.leftExclusive l r →
      l ∈ A.closureAtSet z)
    (hR : ∀ z : V, z ∈ A.rightExclusive l r →
      r ∈ A.closureAtSet z) :
    A.FreeDecomposition where
  left := A.leftRegion l r
  right := A.rightRegion l r
  left_closed := f.leftRegion_isClosed act hf hne hlr hL hR
  right_closed := f.rightRegion_isClosed act hf hne hlr hL hR
  cover := leftRegion_union_rightRegion A l r
  left_proper := f.leftRegion_proper act hf hne hlr hL hR
  right_proper := f.rightRegion_proper act hf hne hlr hL hR
  rel_local := by
    intro n R xs hRel
    exact f.fiveRegion_relation_local
      act hf hne hlr hL hR R xs hRel
  func_cross_empty := by
    intro n F xs hCross
    exact fiveRegion_function_cross_empty A l r F xs hCross

end Homomorphism
end Structure
end AllThoseEPPA
