import Mathlib.Data.Fintype.EquivFin
import AllThoseEPPA.TreeLikeFullAAmalgamation

/-!
# Finiteness and designated copies in full-A tree amalgamations

The recursive predicate `TreeAmalgamation act A C` is the paper's
literal construction of structures from full copies of A.
Two basic invariants are useful for the eventual Lemma `lem:cuts`:

* if A is finite, **every tree amalgamation is finite**, even
  though its carrier changes in each recursive gluing step;
* every tree amalgamation contains a genuine Γ-structure
  embedding of the full original A.

Both arguments use the concrete carrier/embedding construction,
not an abstract statement that unspecified pushouts exist.
These are supporting facts; irreducible extension and the
embedding of B into such a tree are later obligations.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} {Γ : Type w} [Group Γ]
variable {U : Type v}

/-- Recursive amalgamation of full copies of a finite A never
introduces an infinite carrier. -/
theorem TreeAmalgamation.carrier_finite
    (act : L.Action Γ) (A : Structure L U)
    [Finite U]
    {V : Type v} {B : Structure L V}
    (h : TreeAmalgamation act A B) :
    Finite V := by
  induction h with
  | copy C f hSurj =>
      exact Finite.of_surjective f.toFun hSurj
  | glue C B₁ B₂ h₁ h₂ δ₁ δ₂ α₁ α₂ ih₁ ih₂ =>
      letI : Finite _ := ih₁
      letI : Finite _ := ih₂
      exact amalgamCarrier_finite
        (α₁.comp δ₁).toFun (α₂.comp δ₂).toFun

/-- A full A-copy is present in *every* tree amalgamation.
The statement is existential about a genuine Γ-embedding
whose function fibres are preserved exactly. -/
theorem TreeAmalgamation.contains_A
    (act : L.Action Γ) (A : Structure L U)
    {V : Type v} {B : Structure L V}
    (h : TreeAmalgamation act A B) :
    Nonempty (Structure.Embedding act A B) := by
  cases h with
  | copy C f _ =>
      exact ⟨f⟩
  | glue C B₁ B₂ h₁ h₂ δ₁ δ₂ α₁ α₂ =>
      exact ⟨(generalAmalgamLeftEmbedding act
        (α₁.comp δ₁) (α₂.comp δ₂)).comp α₁⟩

end TreeLike
end AllThoseEPPA
