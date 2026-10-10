import Mathlib.Data.Set.Card
import AllThoseEPPA.HerwigLascarForbiddenFamily
import AllThoseEPPA.UnaryHomEmbClosedRangeFactor

/-!
# Small closed images of forbidden homomorphism-embeddings

The first contradiction step in the Herwig--Lascar theorem does not
need to know how the locally tree-like witness was constructed.

A forbidden homomorphism-embedding into a unary-function structure B
has a function-closed image S of size bounded by the finite forbidden
family. Its factorization through the actual induced S is again a
homomorphism-embedding. Consequently, if *every* such small closed
substructure of B homomorphism-embeds in an ambient model M avoiding
the forbidden family, then B itself avoids that family.

In particular, this lemma makes the later use of the complete-E
tree construction independent from the combinatorics of finite
forbidden families.
-/

namespace AllThoseEPPA
namespace HerwigLascar
namespace FiniteForbiddenFamily

universe u v w x y z

variable {L : Language.{u}} [L.HasUnaryFunctions]

/-- The image of a forbidden carrier under any map is uniformly
bounded by the maximum forbidden vertex count. In particular, the
map need not be injective. -/
theorem range_ncard_le_maxCard
    (F : FiniteForbiddenFamily.{u,v,w} L)
    {Γ : Type x} [Group Γ] (act : L.Action Γ)
    (i : F.Code) {W : Type y} (B : Structure L W)
    (g : Structure.Homomorphism act (F.model i) B) :
    (Set.range g.toFun).ncard ≤ F.maxCard := by
  letI : Finite (F.Carrier i) := F.finiteCarrier i
  have hImage :=
    Set.ncard_image_le
      (f := g.toFun) (s := (Set.univ : Set (F.Carrier i)))
      Set.finite_univ
  have hBound :
      (Set.range g.toFun).ncard ≤ Nat.card (F.Carrier i) := by
    simpa only [Set.image_univ, Set.ncard_univ] using hImage
  exact hBound.trans (F.card_le_maxCard i)

/-- Abstract forbidden-obstruction principle.

If every closed induced substructure of B of at most maxCard(F)
vertices homomorphism-embeds into M, and M avoids F, then B
avoids F. This is valid for a possibly infinite ambient M, a
finite (possibly empty) heterogeneous forbidden family and
nontrivial Γ-symbol permutations. No global injectivity of the
forbidden map is assumed. -/
theorem avoids_of_smallClosedHomEmbeds
    (F : FiniteForbiddenFamily.{u,v,w} L)
    {Γ : Type x} [Group Γ] (act : L.Action Γ)
    {W : Type y} {M : Type z}
    (B : Structure L W) (N : Structure L M)
    (hN : F.Avoids act N)
    (hSmall :
      ∀ (S : Set W) (hS : B.IsClosed S),
        S.ncard ≤ F.maxCard →
          ∃ f : Structure.Homomorphism act (B.induce S hS) N,
            Structure.Homomorphism.IsHomomorphismEmbedding act f) :
    F.Avoids act B := by
  intro i hBad
  obtain ⟨g, hg⟩ := hBad
  let S : Set W := Set.range g.toFun
  have hS : B.IsClosed S :=
    Structure.Homomorphism.range_isClosed_of_unary act g hg
  have hCard : S.ncard ≤ F.maxCard :=
    F.range_ncard_le_maxCard act i B g
  obtain ⟨f, hf⟩ := hSmall S hS hCard
  have hAvoidS : F.Avoids act (B.induce S hS) :=
    F.avoids_of_homomorphismEmbedding act hN f hf
  exact hAvoidS i ⟨g.toClosedRange_unary act hg,
    Structure.Homomorphism.toClosedRange_unary_isHomomorphismEmbedding
      act g hg⟩

end FiniteForbiddenFamily
end HerwigLascar
end AllThoseEPPA
