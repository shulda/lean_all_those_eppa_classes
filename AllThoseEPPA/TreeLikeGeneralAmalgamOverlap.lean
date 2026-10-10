import AllThoseEPPA.TreeLikeAmalgamGeneral

/-!
# Exact overlap of two Γ-embedded sources in the general amalgam

The constructed free amalgam of two structures over C is a
**strong amalgam**: its canonical exact Γ-embeddings identify
no additional vertices. Its two source images overlap precisely
on the images of the specified common interface C.

This result is an elementary yet central ingredient in the
eventual pushout universal property needed by manuscript
Lemma `lem:cuts`. It holds without matching language
permutations, without finiteness, and without assumptions on
relation or set-valued function arities.

The proof is grounded in the explicitly constructed carrier
`AmalgamCarrier`, not an abstract quotient or postulated
pushout property.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- **Exact intersection of embedded source copies.**
One vertex from B₁ and one vertex from B₂ represent the
same point of the explicit general-Γ amalgam iff they
are the two prescribed images of a *single* vertex of C. -/
theorem generalAmalgam_source_overlap_iff
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (x : X) (y : Y) :
    generalAmalgamLeftEmbedding act f g x =
      generalAmalgamRightEmbedding act f g y ↔
      ∃ i : I, x = f i ∧ y = g i := by
  change amalgamLeft f.toFun g.toFun x =
    amalgamRight f.toFun g.toFun y ↔
      ∃ i : I, x = f i ∧ y = g i
  exact amalgamLeft_eq_amalgamRight_iff
    f.toFun g.toFun g.injective x y

/-- A second equivalent formulation useful when eliminating a
vertex in the right source which also occurs in the left:
it must come from the exact gluing interface. -/
theorem generalAmalgam_right_in_left_iff
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (y : Y) :
    generalAmalgamRightEmbedding act f g y ∈
        Set.range (generalAmalgamLeftEmbedding act f g).toFun ↔
      y ∈ Set.range g.toFun := by
  constructor
  · rintro ⟨x, hx⟩
    have hEq : generalAmalgamLeftEmbedding act f g x =
        generalAmalgamRightEmbedding act f g y := hx
    obtain ⟨i, _, hyi⟩ :=
      (generalAmalgam_source_overlap_iff act f g x y).mp hEq
    exact ⟨i, hyi.symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨f i, ?_⟩
    exact generalAmalgam_gluing_agrees act f g i

/-- Symmetrically, a left-source vertex in the right source's
image must lie on the exact interface. -/
theorem generalAmalgam_left_in_right_iff
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (x : X) :
    generalAmalgamLeftEmbedding act f g x ∈
        Set.range (generalAmalgamRightEmbedding act f g).toFun ↔
      x ∈ Set.range f.toFun := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨i, hxi, _⟩ :=
      (generalAmalgam_source_overlap_iff act f g x y).mp hy.symm
    exact ⟨i, hxi.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨g i, (generalAmalgam_gluing_agrees act f g i).symm⟩

end TreeLike
end AllThoseEPPA
