import AllThoseEPPA.StrongCompletionTwoClosureGeometry
import AllThoseEPPA.StrongCompletionFibreBijection

/-!
# Explicit vertex collapse of two identified one-point closures

For a Γ-homomorphism-embedding f:A→B and a pair of distinct
vertices a,b with f(a)=f(b), the restrictions of f to
Cl_A(a) and Cl_A(b) have the same image and are injective.

The map constructed here replaces each point of
Cl_A(b) ∖ Cl_A(a) with its uniquely corresponding vertex
of Cl_A(a), leaving all remaining vertices fixed.

This is the *underlying vertex map* of the local quotient
needed in the proof of Proposition 11.3. We prove that:

* it preserves the value of f at every vertex;
* it fixes Cl_A(a) pointwise;
* it maps b to a and is consequently noninjective;
* any new collision has one input in Cl_A(a) and the
  other in Cl_A(b), with the same f-image.

The remaining task is to equip the quotient with an
appropriate Γ-structure and verify that both resulting
maps are homomorphism-embeddings. None of those unproved
structure-level properties are asserted here.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- Collapse the right-hand closure onto its matching left
closure, retaining all vertices outside the right-exclusive
part. The matched representative is canonical by local
injectivity of the original homomorphism-embedding. -/
noncomputable def collapseRightClosure
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) : V → V := by
  classical
  intro x
  exact if hx : x ∈ A.rightExclusive a b then
    (f.closureFibreEquiv act hf hab.symm ⟨x, hx.1⟩).1
    else x

/-- Outside the right-exclusive part no vertex changes. -/
theorem collapseRightClosure_eq_of_not_mem
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b)
    {x : V} (hx : x ∉ A.rightExclusive a b) :
    f.collapseRightClosure act hf hab x = x := by
  simp [collapseRightClosure, hx]

/-- Collapsed vertices lie in the left one-point closure. -/
theorem collapseRightClosure_mem_left
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b)
    {x : V} (hx : x ∈ A.rightExclusive a b) :
    f.collapseRightClosure act hf hab x ∈ A.closureAtSet a := by
  simp only [collapseRightClosure, dif_pos hx]
  exact (f.closureFibreEquiv act hf hab.symm ⟨x, hx.1⟩).2

/-- The original f factors through the collapse at vertex level:
collapsing never changes the f-value. -/
theorem collapseRightClosure_preserves_f
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b)
    (x : V) :
    f (f.collapseRightClosure act hf hab x) = f x := by
  classical
  by_cases hx : x ∈ A.rightExclusive a b
  · simp only [collapseRightClosure, dif_pos hx]
    exact f.closureFibreEquiv_map act hf hab.symm ⟨x, hx.1⟩
  · rw [f.collapseRightClosure_eq_of_not_mem act hf hab hx]

/-- Every point of the chosen left closure is fixed. -/
theorem collapseRightClosure_fixes_left
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b)
    {x : V} (hx : x ∈ A.closureAtSet a) :
    f.collapseRightClosure act hf hab x = x := by
  apply f.collapseRightClosure_eq_of_not_mem act hf hab
  intro hxRight
  exact hxRight.2 hx

/-- The right generator is sent exactly to the left generator. -/
theorem collapseRightClosure_sends_right_to_left
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hne : a ≠ b) (hab : f a = f b) :
    f.collapseRightClosure act hf hab b = a := by
  have hb : b ∈ A.rightExclusive a b :=
    f.right_mem_rightExclusive_of_collision act hf hne hab
  have hU :
      f.collapseRightClosure act hf hab b ∈ A.closureAtSet a :=
    f.collapseRightClosure_mem_left act hf hab hb
  have hVal : f (f.collapseRightClosure act hf hab b) = f a :=
    (f.collapseRightClosure_preserves_f act hf hab b).trans hab.symm
  exact (f.injOn_closureAt act hf a) hU
    (A.mem_closureAtSet a) hVal

/-- The local collapse is genuinely noninjective whenever
a and b are distinct vertices of the same f-fibre. -/
theorem collapseRightClosure_not_injective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hne : a ≠ b) (hab : f a = f b) :
    ¬ Function.Injective (f.collapseRightClosure act hf hab) := by
  intro hInj
  have hA : f.collapseRightClosure act hf hab a = a :=
    f.collapseRightClosure_fixes_left act hf hab
      (A.mem_closureAtSet a)
  have hB : f.collapseRightClosure act hf hab b = a :=
    f.collapseRightClosure_sends_right_to_left act hf hne hab
  exact hne (hInj (hA.trans hB.symm))

/-- The range of the collapse misses the right-exclusive
part: every moved vertex is sent into the left closure,
while every unchanged vertex was already outside it. -/
theorem collapseRightClosure_range_avoids_rightExclusive
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b)
    (x : V) :
    f.collapseRightClosure act hf hab x ∉ A.rightExclusive a b := by
  classical
  by_cases hx : x ∈ A.rightExclusive a b
  · have hU := f.collapseRightClosure_mem_left act hf hab hx
    intro hr
    exact hr.2 hU
  · rw [f.collapseRightClosure_eq_of_not_mem act hf hab hx]
    exact hx

/-- Every nontrivial collision of the normalization comes
from one vertex of the left closure and one of the right
closure. In particular, the operation introduces NO
identifications elsewhere in the structure. -/
theorem collapseRightClosure_collisions_only_cross
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b)
    {x y : V} (hne : x ≠ y)
    (hxy : f.collapseRightClosure act hf hab x =
      f.collapseRightClosure act hf hab y) :
    (x ∈ A.closureAtSet b ∧ y ∈ A.closureAtSet a ∧ f x = f y) ∨
      (x ∈ A.closureAtSet a ∧ y ∈ A.closureAtSet b ∧ f x = f y) := by
  classical
  have hfxfy : f x = f y := by
    calc
      f x = f (f.collapseRightClosure act hf hab x) :=
        (f.collapseRightClosure_preserves_f act hf hab x).symm
      _ = f (f.collapseRightClosure act hf hab y) := by rw [hxy]
      _ = f y :=
        f.collapseRightClosure_preserves_f act hf hab y
  by_cases hx : x ∈ A.rightExclusive a b
  · by_cases hy : y ∈ A.rightExclusive a b
    · have hEq : x = y :=
        (f.injOn_closureAt act hf b) hx.1 hy.1 hfxfy
      exact False.elim (hne hEq)
    · have hny : f.collapseRightClosure act hf hab y = y :=
        f.collapseRightClosure_eq_of_not_mem act hf hab hy
      have hleft : y ∈ A.closureAtSet a := by
        have hnx : f.collapseRightClosure act hf hab x ∈
            A.closureAtSet a :=
          f.collapseRightClosure_mem_left act hf hab hx
        rw [hny] at hxy
        rw [← hxy]
        exact hnx
      exact Or.inl ⟨hx.1, hleft, hfxfy⟩
  · by_cases hy : y ∈ A.rightExclusive a b
    · have hnx : f.collapseRightClosure act hf hab x = x :=
        f.collapseRightClosure_eq_of_not_mem act hf hab hx
      have hleft : x ∈ A.closureAtSet a := by
        have hny : f.collapseRightClosure act hf hab y ∈
            A.closureAtSet a :=
          f.collapseRightClosure_mem_left act hf hab hy
        rw [hnx] at hxy
        rw [hxy]
        exact hny
      exact Or.inr ⟨hleft, hy.1, hfxfy⟩
    · have hnx : f.collapseRightClosure act hf hab x = x :=
        f.collapseRightClosure_eq_of_not_mem act hf hab hx
      have hny : f.collapseRightClosure act hf hab y = y :=
        f.collapseRightClosure_eq_of_not_mem act hf hab hy
      exact False.elim (hne (by simpa only [hnx, hny] using hxy))

end Homomorphism
end Structure
end AllThoseEPPA
