import AllThoseEPPA.StrongCompletionHereditaryStrongAmalgamation

/-!
# Exact statement of the ordinary-to-strong completion problem

The manuscript's Proposition 11.3 is independent of Theorem 1.6
in our proof, but remains a substantive mathematical target.

A completion is merely a homomorphism-embedding into a member
of K. A *strong* completion is additionally injective. It does
NOT require automorphism-preserving lifts: that is a strictly
stronger, separate notion already formalized.

We distinguish these notions explicitly, encode the full
ordinary-to-strong implication for a hereditary finite strong
amalgamation class, and prove the easy direction together with
useful constructors. The converse is a named *proof goal*, not
an axiom or an asserted proved theorem.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

namespace FiniteAmalgamationClass

/-- A genuine strong completion: the map is both a Γ-
homomorphism-embedding and globally injective. The class
target is finite. No lift of automorphisms is required. -/
def HasStrongCompletion
    {act : L.Action Γ}
    (K : FiniteAmalgamationClass act)
    {V : Type v} (A : Structure L V) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (B : Structure L W),
    K.mem B ∧
      ∃ f : Structure.Homomorphism act A B,
        Structure.Homomorphism.IsHomomorphismEmbedding act f ∧
          Function.Injective f.toFun

/-- Every strong completion is an ordinary completion. -/
theorem hasCompletion_of_hasStrongCompletion
    {act : L.Action Γ}
    (K : FiniteAmalgamationClass act)
    {V : Type v} (A : Structure L V)
    (h : K.HasStrongCompletion A) :
    K.HasCompletion A := by
  obtain ⟨W, hW, B, hB, f, hf, _⟩ := h
  exact ⟨W, hW, B, hB, f, hf⟩

/-- Every exact Γ-embedding into a finite class member is in
particular a strong completion. -/
theorem hasStrongCompletion_of_embedding
    {act : L.Action Γ}
    (K : FiniteAmalgamationClass act)
    {V W : Type v} (A : Structure L V) (B : Structure L W)
    [Finite W] (hB : K.mem B)
    (e : Structure.Embedding act A B) :
    K.HasStrongCompletion A := by
  refine ⟨W, inferInstance, B, hB, e.toHomomorphism, ?_, e.injective⟩
  exact Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding
    act e

end FiniteAmalgamationClass

namespace HereditaryFiniteStrongAmalgamationClass

/-- EXACT OPEN TARGET of manuscript Proposition 11.3.

For finite A and a hereditary class K of finite irreducibles
with strong amalgamation, every ordinary K-completion is
equivalent to a strong K-completion. The easy direction is
already proved above; the reverse direction is the substantive
minimal-kernel / five-part argument still to be formalized. -/
def CanUpgradeCompletions
    {act : L.Action Γ}
    (K : HereditaryFiniteStrongAmalgamationClass act) : Prop :=
  ∀ {V : Type v} [Finite V] (A : Structure L V),
    K.toAmalgamationClass.HasCompletion A →
      K.toAmalgamationClass.HasStrongCompletion A

/-- The proposition's claimed iff, conditional on the
explicit as-yet-unproved upgrade property. No hidden axioms. -/
theorem completion_iff_strongCompletion_of_upgrade
    {act : L.Action Γ}
    (K : HereditaryFiniteStrongAmalgamationClass act)
    (hUpgrade : K.CanUpgradeCompletions)
    {V : Type v} [Finite V] (A : Structure L V) :
    K.toAmalgamationClass.HasCompletion A ↔
      K.toAmalgamationClass.HasStrongCompletion A := by
  constructor
  · exact hUpgrade A
  · exact K.toAmalgamationClass.hasCompletion_of_hasStrongCompletion A

end HereditaryFiniteStrongAmalgamationClass
end TreeLike
end AllThoseEPPA
