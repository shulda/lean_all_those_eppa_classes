import AllThoseEPPA.Irreducible

/-!
# The universal carrier map out of a genuine free decomposition

A free decomposition of B has two closed sides covering the
entire carrier. If maps from the induced sides into a common
type agree on their exact intersection, they glue uniquely to
one map on the entire carrier of B.

We prove the gluing map agrees with each side on all vertices,
including vertices belonging to both sides. We also prove the
precise injectivity criterion needed for constructing a
Γ-structure embedding into an actual amalgam: injectivity
on each side, together with the requirement that cross-side
identifications arise only from a single common vertex.

This file concerns only the **carrier-level** universal
property. Relation reflection and exact preservation of
set-valued function fibres are subsequent obligations of the
full Γ-amalgam universal-property theorem.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- Since a free decomposition covers all vertices, a point
outside the left side belongs to the right side. -/
theorem freeCut_right_of_not_left
    {B : Structure L V} (d : B.FreeDecomposition)
    {x : V} (hx : x ∉ d.left) : x ∈ d.right := by
  have hCover : x ∈ d.left ∪ d.right := by
    rw [d.cover]
    exact Set.mem_univ x
  exact hCover.resolve_left hx

/-- A concrete map on B glued from two maps on the two closed
sides. No agreement hypothesis is needed to *define* it:
we always prefer the left map where both are available. -/
noncomputable def glueFreeCutMap
    {B : Structure L V} (d : B.FreeDecomposition)
    (l : d.left → W) (r : d.right → W) : V → W := by
  classical
  intro x
  exact if hx : x ∈ d.left then l ⟨x, hx⟩
    else r ⟨x, freeCut_right_of_not_left d hx⟩

/-- The glued map agrees with the left-side map without any
additional compatibility assumptions. -/
theorem glueFreeCutMap_left
    {B : Structure L V} (d : B.FreeDecomposition)
    (l : d.left → W) (r : d.right → W)
    (x : V) (hx : x ∈ d.left) :
    glueFreeCutMap d l r x = l ⟨x, hx⟩ := by
  classical
  simp [glueFreeCutMap, hx]

/-- If two maps agree at every common vertex, the glued map
also agrees with the right-side map, including on the overlap. -/
theorem glueFreeCutMap_right
    {B : Structure L V} (d : B.FreeDecomposition)
    (l : d.left → W) (r : d.right → W)
    (hAgree :
      ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    (x : V) (hx : x ∈ d.right) :
    glueFreeCutMap d l r x = r ⟨x, hx⟩ := by
  classical
  by_cases hxL : x ∈ d.left
  · rw [glueFreeCutMap_left d l r x hxL]
    exact hAgree x hxL hx
  · simp [glueFreeCutMap, hxL]

/-- The glued map is the unique map extending both specified
source maps, provided they coincide on the common interface. -/
theorem glueFreeCutMap_unique
    {B : Structure L V} (d : B.FreeDecomposition)
    (l : d.left → W) (r : d.right → W)
    (hAgree :
      ∀ (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        l ⟨x, hxL⟩ = r ⟨x, hxR⟩)
    (f : V → W)
    (hfL : ∀ (x : V) (hx : x ∈ d.left),
      f x = l ⟨x, hx⟩)
    (hfR : ∀ (x : V) (hx : x ∈ d.right),
      f x = r ⟨x, hx⟩) :
    f = glueFreeCutMap d l r := by
  funext x
  by_cases hx : x ∈ d.left
  · rw [hfL x hx, glueFreeCutMap_left d l r x hx]
  · have hR : x ∈ d.right := freeCut_right_of_not_left d hx
    rw [hfR x hR, glueFreeCutMap_right d l r hAgree x hR]

/-- A glued map is injective if its restrictions to the two
sides are injective and the two side images overlap only at
points representing **the same original vertex**. This is the
pure carrier part of the embedding universal property. -/
theorem glueFreeCutMap_injective
    {B : Structure L V} (d : B.FreeDecomposition)
    (l : d.left → W) (r : d.right → W)
    (hLeft : Function.Injective l)
    (hRight : Function.Injective r)
    (hCross : ∀ (x : d.left) (y : d.right),
      l x = r y → x.1 = y.1) :
    Function.Injective (glueFreeCutMap d l r) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ d.left
  · by_cases hy : y ∈ d.left
    · have h : l ⟨x, hx⟩ = l ⟨y, hy⟩ := by
        simpa only [glueFreeCutMap_left d l r x hx,
          glueFreeCutMap_left d l r y hy] using hxy
      exact congrArg Subtype.val (hLeft h)
    · have hyR : y ∈ d.right := freeCut_right_of_not_left d hy
      have h : l ⟨x, hx⟩ = r ⟨y, hyR⟩ := by
        simpa [glueFreeCutMap, hx, hy] using hxy
      exact hCross ⟨x, hx⟩ ⟨y, hyR⟩ h
  · have hxR : x ∈ d.right := freeCut_right_of_not_left d hx
    by_cases hy : y ∈ d.left
    · have h : r ⟨x, hxR⟩ = l ⟨y, hy⟩ := by
        simpa [glueFreeCutMap, hx, hy] using hxy
      exact (hCross ⟨y, hy⟩ ⟨x, hxR⟩ h.symm).symm
    · have hyR : y ∈ d.right := freeCut_right_of_not_left d hy
      have h : r ⟨x, hxR⟩ = r ⟨y, hyR⟩ := by
        simpa only [glueFreeCutMap, dif_neg hx, dif_neg hy] using hxy
      exact congrArg Subtype.val (hRight h)

end TreeLike
end AllThoseEPPA
