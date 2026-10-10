import AllThoseEPPA.TreeLikeFreeCutPushoutSupport

/-!
# The concrete free-cut Γ-amalgam universal-property embedding

This is the central constructive gluing lemma needed for the
paper's `lem:cuts`: if B is the free amalgamation of two
closed induced sides, and those sides embed exactly in two
arbitrary Γ-structures H₁ and H₂, then B embeds **exactly**
into the concrete general-Γ amalgam of H₁ and H₂ along the
corresponding images of B's closed common base.

Crucially, the source B itself embeds into the target:
we do not merely construct a quotient set, a homomorphism,
or independent embeddings of its sides. In the resulting
embedding, relations are preserved AND reflected, and
function-value fibres agree as sets for all arities.

The proof assembles the independently checked components:

* exact closed-base embeddings;
* concrete arbitrary-language Γ-pushout of two structures;
* equal resulting language components and pointwise
  agreement on the base;
* exact cross-side injectivity;
* reflection of support in both free covers;
* the generic universal `glueFreeCutEmbedding` theorem
  (relation reflection and exact function fibre equality).

This is still only the local gluing step. The full `lem:cuts`
requires induction over `ACliqueTree`, use of full embedded
copies of A at each base, and obtaining the resulting tree.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {X : Type x} {Y : Type y}

/-- **Concrete Γ-free-amalgamation universal property**:
the original freely decomposed B embeds exactly into the
amalgam of any two ambient target structures receiving exact
embeddings of B's closed sides.

No finite-carrier assumption, no unary-functions assumption,
no equality of the original side embeddings' Γ-language
components, and no relation-arity restrictions. -/
noncomputable def freeCutPushoutEmbedding
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂) :
    Structure.Embedding act B (freeCutPushoutStructure act B d eL eR) :=
  glueFreeCutEmbedding act B d
    (freeCutPushoutStructure act B d eL eR)
    (freeCutPushoutCover act B d eL eR)
    (freeCutPushoutSideLeft act B d eL eR)
    (freeCutPushoutSideRight act B d eL eR)
    (freeCutPushoutSide_lang_eq act B d eL eR)
    (freeCutPushoutSide_agree act B d eL eR)
    (freeCutPushoutSide_cross_eq act B d eL eR)
    (freeCutPushout_left_support act B d eL eR)
    (freeCutPushout_right_support act B d eL eR)

/-- This exact embedding restricts to the corresponding
composite left-side embedding on all original vertices of
the left part of B. -/
theorem freeCutPushoutEmbedding_left
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂)
    (x : V) (hx : x ∈ d.left) :
    freeCutPushoutEmbedding act B d eL eR x =
      freeCutPushoutSideLeft act B d eL eR ⟨x, hx⟩ :=
  glueFreeCutMap_left d
    (freeCutPushoutSideLeft act B d eL eR).toFun
    (freeCutPushoutSideRight act B d eL eR).toFun x hx

/-- The analogous restriction to the right original side. -/
theorem freeCutPushoutEmbedding_right
    (act : L.Action Γ)
    (B : Structure L V) (d : B.FreeDecomposition)
    {H₁ : Structure L X} {H₂ : Structure L Y}
    (eL : Structure.Embedding act (B.induce d.left d.left_closed) H₁)
    (eR : Structure.Embedding act (B.induce d.right d.right_closed) H₂)
    (x : V) (hx : x ∈ d.right) :
    freeCutPushoutEmbedding act B d eL eR x =
      freeCutPushoutSideRight act B d eL eR ⟨x, hx⟩ :=
  glueFreeCutMap_right d
    (freeCutPushoutSideLeft act B d eL eR).toFun
    (freeCutPushoutSideRight act B d eL eR).toFun
    (freeCutPushoutSide_agree act B d eL eR) x hx

end TreeLike
end AllThoseEPPA
