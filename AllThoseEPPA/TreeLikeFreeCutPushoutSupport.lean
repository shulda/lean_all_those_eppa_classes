import AllThoseEPPA.TreeLikeFreeCutPushoutMaps

/-!
# Exact side-support reflection in the constructed free-cut Γ-pushout

The previous module built the two composite exact Γ-embeddings
of the induced sides of a free decomposition B into the explicit
amalgam of the two target structures. They agree on the common
base and are jointly injective.

For the universal exact embedding theorem we must additionally
show that the glued map of the original B **reflects side
membership**: if the image of a vertex belongs to the left
(resp. right) whole target structure, then the original
vertex already belonged to the corresponding left (resp.
right) side of B.

The converse is immediate from the side embeddings. The
nontrivial direction uses *strong* (exact-interface-only)
overlap of the target Γ-amalgam: a vertex from the opposite
side cannot enter the target source except through the
common interface, and injectivity of the original side
embeddings brings the vertex back to B's exact intersection.

This is the final geometric hypothesis needed for the
generic `glueFreeCutEmbedding` universal-property theorem.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {X : Type x} {Y : Type y}

/-- The canonical (possibly degenerate) free cover of the
actual general Γ-amalgam of the target structures, along
the exact common base of the original B. -/
noncomputable def freeCutPushoutCover
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂) :
    (freeCutPushoutStructure act B d eL eR).FreeCover :=
  amalgamFreeCover act
    (freeCutPushoutBaseLeft act B d eL)
    (alignedRightEmbedding act
      (freeCutPushoutBaseLeft act B d eL)
      (freeCutPushoutBaseRight act B d eR))
    (alignedRightEmbedding_lang_eq act
      (freeCutPushoutBaseLeft act B d eL)
      (freeCutPushoutBaseRight act B d eR))

/-- A vertex of B is sent to the left *whole source side* of
its target amalgam exactly when it was originally in the left
closed side of the free decomposition. -/
theorem freeCutPushout_left_support
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂)
    (x : V) :
    glueFreeCutMap d
        (freeCutPushoutSideLeft act B d eL eR).toFun
        (freeCutPushoutSideRight act B d eL eR).toFun x ∈
      (freeCutPushoutCover act B d eL eR).left ↔
        x ∈ d.left := by
  let f := freeCutPushoutBaseLeft act B d eL
  let g := freeCutPushoutBaseRight act B d eR
  let l := freeCutPushoutSideLeft act B d eL eR
  let r := freeCutPushoutSideRight act B d eL eR
  have hAgree : ∀ (z : V) (hzL : z ∈ d.left) (hzR : z ∈ d.right),
      l ⟨z, hzL⟩ = r ⟨z, hzR⟩ :=
    freeCutPushoutSide_agree act B d eL eR
  change glueFreeCutMap d l.toFun r.toFun x ∈
    Set.range (generalAmalgamLeftEmbedding act f g).toFun ↔
      x ∈ d.left
  constructor
  · intro hMem
    by_contra hx
    have hxR : x ∈ d.right := freeCut_right_of_not_left d hx
    have hRight :
        generalAmalgamRightEmbedding act f g (eR ⟨x, hxR⟩) ∈
          Set.range (generalAmalgamLeftEmbedding act f g).toFun := by
      rw [glueFreeCutMap_right d l.toFun r.toFun
        hAgree x hxR] at hMem
      exact hMem
    obtain ⟨s, hs⟩ :=
      (generalAmalgam_right_in_left_iff act f g
        (eR ⟨x, hxR⟩)).mp hRight
    have hs' : eR ⟨x, hxR⟩ =
        eR (freeCut_baseToRight act B d s) := hs
    have hsub := eR.injective hs'
    have hxx : x = s.1 := by
      calc
        x = (freeCut_baseToRight act B d s).1 :=
          congrArg Subtype.val hsub
        _ = s.1 := freeCut_baseToRight_val act B d s
    exact hx (hxx ▸ s.2.1)
  · intro hx
    refine ⟨eL ⟨x, hx⟩, ?_⟩
    exact (glueFreeCutMap_left d l.toFun r.toFun x hx).symm

/-- Symmetric exact reflection for the right whole source
side of the target amalgam. -/
theorem freeCutPushout_right_support
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂)
    (x : V) :
    glueFreeCutMap d
        (freeCutPushoutSideLeft act B d eL eR).toFun
        (freeCutPushoutSideRight act B d eL eR).toFun x ∈
      (freeCutPushoutCover act B d eL eR).right ↔
        x ∈ d.right := by
  let f := freeCutPushoutBaseLeft act B d eL
  let g := freeCutPushoutBaseRight act B d eR
  let l := freeCutPushoutSideLeft act B d eL eR
  let r := freeCutPushoutSideRight act B d eL eR
  have hAgree : ∀ (z : V) (hzL : z ∈ d.left) (hzR : z ∈ d.right),
      l ⟨z, hzL⟩ = r ⟨z, hzR⟩ :=
    freeCutPushoutSide_agree act B d eL eR
  change glueFreeCutMap d l.toFun r.toFun x ∈
    Set.range (generalAmalgamRightEmbedding act f g).toFun ↔
      x ∈ d.right
  constructor
  · intro hMem
    by_contra hx
    have hxL : x ∈ d.left := by
      have hCover : x ∈ d.left ∪ d.right := by
        rw [d.cover]
        exact Set.mem_univ x
      exact hCover.resolve_right hx
    have hLeft :
        generalAmalgamLeftEmbedding act f g (eL ⟨x, hxL⟩) ∈
          Set.range (generalAmalgamRightEmbedding act f g).toFun := by
      rw [glueFreeCutMap_left d l.toFun r.toFun x hxL] at hMem
      exact hMem
    obtain ⟨s, hs⟩ :=
      (generalAmalgam_left_in_right_iff act f g
        (eL ⟨x, hxL⟩)).mp hLeft
    have hs' : eL ⟨x, hxL⟩ =
        eL (freeCut_baseToLeft act B d s) := hs
    have hsub := eL.injective hs'
    have hxx : x = s.1 := by
      calc
        x = (freeCut_baseToLeft act B d s).1 :=
          congrArg Subtype.val hsub
        _ = s.1 := freeCut_baseToLeft_val act B d s
    exact hx (hxx ▸ s.2.2)
  · intro hx
    refine ⟨eR ⟨x, hx⟩, ?_⟩
    exact (glueFreeCutMap_right d l.toFun r.toFun
      hAgree x hx).symm

end TreeLike
end AllThoseEPPA
