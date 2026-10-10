import AllThoseEPPA.TreeLikeFreeCutUniversalEmbedding
import AllThoseEPPA.TreeLikeGeneralAmalgamOverlap
import AllThoseEPPA.TreeLikeAmalgamLanguageComponents
import AllThoseEPPA.TreeLikeFreeCutBaseMapIdentities

/-!
# Exact Γ-maps from the sides of a free cut to their general amalgam

Suppose B has a genuine free decomposition, and its closed
induced sides embed exactly into arbitrary Γ-structures H₁,H₂.
The *same actual closed intersection* embeds in both targets.
Use its two composite embeddings to form the concrete general
Γ-amalgam of H₁ and H₂.

This file proves the key interface properties of the induced
maps from B's sides into the amalgam:

* their language components coincide, despite unrelated Γ
  components of the original embeddings;
* they agree pointwise on B's closed common base;
* a cross-side collision forces the two source vertices to
  be the **same original vertex**.

These conditions feed into `glueFreeCutEmbedding`, which also
requires reflection of the target free cover's side support.
No additional relations/functions are assumed.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {X : Type x} {Y : Type y}

/-- Embed the exact common closed base into the target of the
left-side embedding. -/
noncomputable def freeCutPushoutBaseLeft
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁) :
    Structure.Embedding act (freeCut_base B d) H₁ :=
  eL.comp (freeCut_baseToLeft act B d)

/-- Embed the same common closed base into the right target. -/
noncomputable def freeCutPushoutBaseRight
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₂ : Structure L Y}
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂) :
    Structure.Embedding act (freeCut_base B d) H₂ :=
  eR.comp (freeCut_baseToRight act B d)

/-- The explicit general-Γ amalgam of the two larger target
structures, along the prescribed common closed base of B. -/
noncomputable def freeCutPushoutStructure
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂) :
    Structure L (AmalgamCarrier
      (freeCutPushoutBaseLeft act B d eL).toFun
      (freeCutPushoutBaseRight act B d eR).toFun) :=
  generalAmalgamStructure act
    (freeCutPushoutBaseLeft act B d eL)
    (freeCutPushoutBaseRight act B d eR)

/-- The actual embedding of B's left closed side into the
glued target, obtained by composing two exact embeddings. -/
noncomputable def freeCutPushoutSideLeft
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂) :
    Structure.Embedding act (B.induce d.left d.left_closed)
      (freeCutPushoutStructure act B d eL eR) :=
  (generalAmalgamLeftEmbedding act
    (freeCutPushoutBaseLeft act B d eL)
    (freeCutPushoutBaseRight act B d eR)).comp eL

/-- The actual embedding of B's right closed side into the
same target, with automatic Γ-language relabelling. -/
noncomputable def freeCutPushoutSideRight
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂) :
    Structure.Embedding act (B.induce d.right d.right_closed)
      (freeCutPushoutStructure act B d eL eR) :=
  (generalAmalgamRightEmbedding act
    (freeCutPushoutBaseLeft act B d eL)
    (freeCutPushoutBaseRight act B d eR)).comp eR

/-- The two induced embeddings of B's sides have identical
Γ-language components after relabelling, even when eL.lang
and eR.lang were initially unrelated. -/
theorem freeCutPushoutSide_lang_eq
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂) :
    (freeCutPushoutSideLeft act B d eL eR).lang =
      (freeCutPushoutSideRight act B d eL eR).lang := by
  simp [freeCutPushoutSideLeft, freeCutPushoutSideRight,
    freeCutPushoutBaseLeft, freeCutPushoutBaseRight,
    Structure.Embedding.comp, mul_assoc]

/-- The induced left and right embeddings literally agree
on every original vertex of the common closed interface. -/
theorem freeCutPushoutSide_agree
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂)
    (x : V) (hxL : x ∈ d.left) (hxR : x ∈ d.right) :
    freeCutPushoutSideLeft act B d eL eR ⟨x, hxL⟩ =
      freeCutPushoutSideRight act B d eL eR ⟨x, hxR⟩ := by
  let s : (d.left ∩ d.right : Set V) := ⟨x, ⟨hxL, hxR⟩⟩
  have hL : freeCut_baseToLeft act B d s = (⟨x, hxL⟩ : d.left) := by
    apply Subtype.ext
    exact freeCut_baseToLeft_val act B d s
  have hR : freeCut_baseToRight act B d s = (⟨x, hxR⟩ : d.right) := by
    apply Subtype.ext
    exact freeCut_baseToRight_val act B d s
  have hGlue := generalAmalgam_gluing_agrees act
    (freeCutPushoutBaseLeft act B d eL)
    (freeCutPushoutBaseRight act B d eR) s
  change
    generalAmalgamLeftEmbedding act
      (freeCutPushoutBaseLeft act B d eL)
      (freeCutPushoutBaseRight act B d eR)
      (eL ⟨x, hxL⟩) =
    generalAmalgamRightEmbedding act
      (freeCutPushoutBaseLeft act B d eL)
      (freeCutPushoutBaseRight act B d eR)
      (eR ⟨x, hxR⟩)
  simpa only [freeCutPushoutBaseLeft, freeCutPushoutBaseRight,
    Structure.Embedding.comp_apply, hL, hR] using hGlue

/-- Two vertices from opposite induced sides can acquire the
same image only if they are the SAME original B-vertex.
This is the crucial cross-side injectivity condition. -/
theorem freeCutPushoutSide_cross_eq
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂)
    (x : d.left) (y : d.right)
    (hxy : freeCutPushoutSideLeft act B d eL eR x =
      freeCutPushoutSideRight act B d eL eR y) :
    x.1 = y.1 := by
  let f := freeCutPushoutBaseLeft act B d eL
  let g := freeCutPushoutBaseRight act B d eR
  have hInter :
      generalAmalgamLeftEmbedding act f g (eL x) =
        generalAmalgamRightEmbedding act f g (eR y) := hxy
  obtain ⟨s, hx, hy⟩ :=
    (generalAmalgam_source_overlap_iff act f g (eL x) (eR y)).mp hInter
  have hx' : eL x = eL (freeCut_baseToLeft act B d s) := hx
  have hy' : eR y = eR (freeCut_baseToRight act B d s) := hy
  have hEqL := eL.injective hx'
  have hEqR := eR.injective hy'
  calc
    x.1 = (freeCut_baseToLeft act B d s).1 :=
      congrArg Subtype.val hEqL
    _ = s.1 := freeCut_baseToLeft_val act B d s
    _ = (freeCut_baseToRight act B d s).1 :=
      (freeCut_baseToRight_val act B d s).symm
    _ = y.1 := (congrArg Subtype.val hEqR).symm

end TreeLike
end AllThoseEPPA
