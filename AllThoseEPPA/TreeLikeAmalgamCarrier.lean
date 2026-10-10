import Mathlib.Data.Fintype.Basic
import AllThoseEPPA.Map

/-!
# Carrier of a free amalgam along injective maps

A subsequent step of `lem:cuts` must glue **full copies of A**
along a substructure already embedded in both sides. The underlying
carrier should not be left implicit or postulated as an axiom.

Given injections `f : I → X` and `g : I → Y`, we retain the
existing vertices X and add precisely the vertices of Y outside
the image of g. The two canonical inclusions agree on I; they are
injective, cover the new carrier, and overlap **exactly on I**.

This file formalizes this underlying pushout-of-injections geometry.
It deliberately contains no interpretation of relation/function
symbols yet. That structure-theoretic step must separately prove
the free-amalgam local interpretations and exact embedding laws.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {I : Type u} {X : Type v} {Y : Type w}

/-- Concrete carrier of a free amalgam: all old X-vertices, plus
exactly those Y-vertices outside the gluing image of g. -/
def AmalgamCarrier (f : I → X) (g : I → Y) : Type (max v w) :=
  X ⊕ {y : Y // y ∉ Set.range g}

/-- The whole left-hand carrier is retained unchanged. -/
def amalgamLeft (f : I → X) (g : I → Y) :
    X → AmalgamCarrier f g :=
  Sum.inl

/-- The right-hand inclusion: vertices in g(I) are identified
with their counterparts f(I), while new vertices are tagged. -/
noncomputable def amalgamRight (f : I → X) (g : I → Y) :
    Y → AmalgamCarrier f g := by
  classical
  intro y
  exact if hy : y ∈ Set.range g then
    Sum.inl (f (Classical.choose hy))
  else
    Sum.inr ⟨y, hy⟩

/-- The left map is automatically injective. -/
theorem amalgamLeft_injective (f : I → X) (g : I → Y) :
    Function.Injective (amalgamLeft f g) :=
  Sum.inl_injective

/-- The right inclusion agrees with the left inclusion on each
identified gluing vertex. -/
theorem amalgamRight_glued (f : I → X) (g : I → Y)
    (hg : Function.Injective g) (i : I) :
    amalgamRight f g (g i) = amalgamLeft f g (f i) := by
  classical
  have hi : g i ∈ Set.range g := ⟨i, rfl⟩
  change (if h : g i ∈ Set.range g then
      (Sum.inl (f (Classical.choose h)) : AmalgamCarrier f g)
    else Sum.inr ⟨g i, h⟩) = Sum.inl (f i)
  simp only [dif_pos hi]
  exact congrArg (fun j : I =>
    (Sum.inl (f j) : AmalgamCarrier f g))
    (hg (Classical.choose_spec hi))

/-- A right vertex outside the interface remains a freshly tagged
right vertex. -/
theorem amalgamRight_outside (f : I → X) (g : I → Y)
    (y : Y) (hy : y ∉ Set.range g) :
    amalgamRight f g y = Sum.inr ⟨y, hy⟩ := by
  classical
  change (if h : y ∈ Set.range g then
      (Sum.inl (f (Classical.choose h)) : AmalgamCarrier f g)
    else Sum.inr ⟨y, h⟩) = Sum.inr ⟨y, hy⟩
  simp only [dif_neg hy]

/-- The right inclusion is injective whenever the gluing maps
are injective. This rules out any accidental identifications
beyond the prescribed common interface. -/
theorem amalgamRight_injective
    (f : I → X) (g : I → Y)
    (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Injective (amalgamRight f g) := by
  intro y z h
  classical
  by_cases hy : y ∈ Set.range g
  · obtain ⟨i, rfl⟩ := hy
    by_cases hz : z ∈ Set.range g
    · obtain ⟨j, rfl⟩ := hz
      rw [amalgamRight_glued f g hg i,
          amalgamRight_glued f g hg j] at h
      have hfi : f i = f j := Sum.inl.inj h
      exact congrArg g (hf hfi)
    · rw [amalgamRight_glued f g hg i,
          amalgamRight_outside f g z hz] at h
      cases h
  · by_cases hz : z ∈ Set.range g
    · obtain ⟨j, rfl⟩ := hz
      rw [amalgamRight_outside f g y hy,
          amalgamRight_glued f g hg j] at h
      cases h
    · rw [amalgamRight_outside f g y hy,
          amalgamRight_outside f g z hz] at h
      have hSub : (⟨y, hy⟩ : {t : Y // t ∉ Set.range g}) =
          ⟨z, hz⟩ := Sum.inr.inj h
      exact congrArg Subtype.val hSub

/-- The images of the two maps meet precisely along the specified
interface. This is the pointwise version, allowing arbitrary
non-surjective gluing embeddings. -/
theorem amalgamLeft_eq_amalgamRight_iff
    (f : I → X) (g : I → Y)
    (hg : Function.Injective g) (x : X) (y : Y) :
    amalgamLeft f g x = amalgamRight f g y ↔
      ∃ i : I, x = f i ∧ y = g i := by
  constructor
  · intro h
    by_cases hy : y ∈ Set.range g
    · obtain ⟨i, rfl⟩ := hy
      rw [amalgamRight_glued f g hg i] at h
      have hEq : x = f i := Sum.inl.inj h
      exact ⟨i, hEq, rfl⟩
    · rw [amalgamRight_outside f g y hy] at h
      cases h
  · rintro ⟨i, rfl, rfl⟩
    exact (amalgamRight_glued f g hg i).symm

/-- Every vertex of the concrete amalgam comes from at least one
of its two source carriers. -/
theorem amalgamCarrier_covered
    (f : I → X) (g : I → Y) :
    Set.range (amalgamLeft f g) ∪
      Set.range (amalgamRight f g) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro z
  cases z with
  | inl x =>
      exact Or.inl ⟨x, rfl⟩
  | inr y =>
      refine Or.inr ⟨y.1, ?_⟩
      have hSubtype :
          (⟨y.1, y.2⟩ : {z : Y // z ∉ Set.range g}) = y :=
        Subtype.ext rfl
      simpa only [hSubtype] using
        (amalgamRight_outside f g y.1 y.2)

/-- No new infinitude is introduced: gluing two finite carriers
has a finite carrier. -/
instance amalgamCarrier_finite (f : I → X) (g : I → Y)
    [Finite X] [Finite Y] :
    Finite (AmalgamCarrier f g) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype Y := Fintype.ofFinite Y
  change Finite (X ⊕ {y : Y // y ∉ Set.range g})
  exact Fintype.finite _

end TreeLike
end AllThoseEPPA
