import Mathlib.Data.Fintype.Card
import AllThoseEPPA.TreeLikeHomEmbComposition

/-!
# Finite forbidden families for the Herwig--Lascar class theorem

The manuscript's generalization of the Herwig--Lascar theorem
concerns classes Forb(F) determined by a finite family F of
finite Γ-structures, allowing each forbidden structure to
have a DIFFERENT finite carrier.

The family uses a finite index type and a dependent family
of finite carrier types. No artificial common vertex type,
chosen enumerations, or cardinality assumptions on ambient
structures are introduced.

Avoidance means absence of Γ-homomorphism-embeddings,
not merely absence of embeddings or ordinary homomorphisms.
The class is downward closed under genuine
homomorphism-embeddings by the checked composition theorem.

A canonical numerical bound on the sizes of all forbidden
carriers is obtained from the finite index type. This is the
n required by the local-tree step of manuscript thm:main.
-/

namespace AllThoseEPPA
namespace HerwigLascar

universe u v w x y z

/-- Finite family of finite forbidden structures, with genuinely
heterogeneous carrier types. The code type itself is finite. -/
structure FiniteForbiddenFamily (L : Language.{u}) where
  Code : Type v
  finiteCode : Finite Code
  Carrier : Code → Type w
  finiteCarrier : ∀ i : Code, Finite (Carrier i)
  model : (i : Code) → Structure L (Carrier i)

namespace FiniteForbiddenFamily

variable {L : Language.{u}}

/-- Largest number of vertices in a forbidden structure
(empty families have numerical bound zero). -/
noncomputable def maxCard
    (F : FiniteForbiddenFamily.{u,v,w} L) : ℕ := by
  classical
  letI : Finite F.Code := F.finiteCode
  letI : Fintype F.Code := Fintype.ofFinite F.Code
  exact Finset.univ.sup (fun i : F.Code => Nat.card (F.Carrier i))

/-- Every forbidden carrier is bounded by maxCard. -/
theorem card_le_maxCard
    (F : FiniteForbiddenFamily.{u,v,w} L)
    (i : F.Code) :
    Nat.card (F.Carrier i) ≤ F.maxCard := by
  classical
  letI : Finite F.Code := F.finiteCode
  letI : Fintype F.Code := Fintype.ofFinite F.Code
  exact Finset.le_sup (Finset.mem_univ i)

/-- Forb(F): no forbidden Γ-structure admits a genuine
homomorphism-embedding into the target structure B.
The action may permute language symbols nontrivially. -/
def Avoids
    (F : FiniteForbiddenFamily.{u,v,w} L)
    {Γ : Type x} [Group Γ]
    (act : L.Action Γ)
    {W : Type y} (B : Structure L W) : Prop :=
  ∀ i : F.Code,
    ¬ ∃ f : Structure.Homomorphism act (F.model i) B,
      Structure.Homomorphism.IsHomomorphismEmbedding act f

/-- Forb(F) is downward closed under any Γ-homomorphism-embedding.
In particular, an embedded induced substructure of a Forb(F)
structure still belongs to Forb(F). -/
theorem avoids_of_homomorphismEmbedding
    (F : FiniteForbiddenFamily.{u,v,w} L)
    {Γ : Type x} [Group Γ] (act : L.Action Γ)
    {V : Type y} {W : Type z}
    {B : Structure L W} {C : Structure L V}
    (hB : F.Avoids act B)
    (f : Structure.Homomorphism act C B)
    (hf : Structure.Homomorphism.IsHomomorphismEmbedding act f) :
    F.Avoids act C := by
  intro i hBad
  obtain ⟨g, hg⟩ := hBad
  exact hB i ⟨f.comp g,
    Structure.Homomorphism.comp_isHomomorphismEmbedding
      act f g hf hg⟩

end FiniteForbiddenFamily
end HerwigLascar
end AllThoseEPPA
