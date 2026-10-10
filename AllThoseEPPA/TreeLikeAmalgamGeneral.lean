import AllThoseEPPA.TreeLikeAmalgamEmbeddings

/-!
# Gluing arbitrary Γ-embeddings by first aligning their languages

The checked concrete amalgam constructor requires two embeddings
of the interface with the same language component. This is not
a restriction on arbitrary Γ-amalgamation.

Given f : C ↪ B₁ and g : C ↪ B₂, relabel B₂ by
`f.lang * g.lang⁻¹`. The map underlying g is unchanged,
but the two embeddings now have equal language components.

Apply the concrete free-amalgam construction and then compose
the right embedding with the exact relabelling embedding
`B₂ ↪ B₂.relabel`. This yields an actual common target
structure and **two exact Γ-embeddings** of the original sides,
even when their initial language components differ.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- The aligned language equation, expressed in the orientation
expected by the two-sided structure constructor. -/
theorem alignedRightEmbedding_lang_eq
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) :
    f.lang = (alignedRightEmbedding act f g).lang :=
  (alignedRightEmbedding_lang act f g).symm

/-- The explicit Γ-amalgam for *arbitrary* embeddings of C into
B₁ and B₂, without an artificial equality-of-language condition. -/
noncomputable def generalAmalgamStructure
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) :
    Structure L (AmalgamCarrier f.toFun g.toFun) :=
  amalgamStructure act f (alignedRightEmbedding act f g)
    (alignedRightEmbedding_lang_eq act f g)

/-- The first original Γ-structure embeds exactly into the
general-language amalgam. -/
noncomputable def generalAmalgamLeftEmbedding
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) :
    Structure.Embedding act B₁ (generalAmalgamStructure act f g) :=
  amalgamLeftEmbedding act f (alignedRightEmbedding act f g)
    (alignedRightEmbedding_lang_eq act f g)

/-- The second original Γ-structure embeds exactly after its
language component is reconciled with that of the first. -/
noncomputable def generalAmalgamRightEmbedding
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) :
    Structure.Embedding act B₂ (generalAmalgamStructure act f g) := by
  let k : Γ := f.lang * g.lang⁻¹
  let relabel : Structure.Embedding act B₂ (B₂.relabel act k) :=
    (Structure.Embedding.id (act := act) B₂).relabelTarget act k
  let aligned :
      Structure.Embedding act (B₂.relabel act k)
        (generalAmalgamStructure act f g) :=
    amalgamRightEmbedding act f (alignedRightEmbedding act f g)
      (alignedRightEmbedding_lang_eq act f g)
  exact aligned.comp relabel

/-- The left source embedding has the original left-inclusion map
on vertices. -/
@[simp] theorem generalAmalgamLeftEmbedding_apply
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) (x : X) :
    generalAmalgamLeftEmbedding act f g x =
      amalgamLeft f.toFun g.toFun x :=
  rfl

/-- The right source embedding has the original right-inclusion
map on vertices, despite the change of the language component. -/
@[simp] theorem generalAmalgamRightEmbedding_apply
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) (y : Y) :
    generalAmalgamRightEmbedding act f g y =
      amalgamRight f.toFun g.toFun y :=
  rfl

/-- The original gluing images agree in the full Γ-amalgam. -/
theorem generalAmalgam_gluing_agrees
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂) (i : I) :
    generalAmalgamLeftEmbedding act f g (f i) =
      generalAmalgamRightEmbedding act f g (g i) := by
  change amalgamLeft f.toFun g.toFun (f i) =
    amalgamRight f.toFun g.toFun (g i)
  exact (amalgamRight_glued f.toFun g.toFun g.injective i).symm

end TreeLike
end AllThoseEPPA
