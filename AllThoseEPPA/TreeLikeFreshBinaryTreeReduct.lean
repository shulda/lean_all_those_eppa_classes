import AllThoseEPPA.TreeLikeFullAAmalgamation
import AllThoseEPPA.TreeLikeFreshBinaryStructure

/-!
# Reduct of recursive full-A tree amalgamations

The original manuscript theorem constructs a literal recursive free
amalgamation of full copies of a complete-E expansion of A. Deleting
E must produce the same recursive gluing construction over A itself.

The concrete amalgam carrier is unchanged by relation reduct. Both
language alignment and right-side relabelling use the same group
elements and the original symbols. Thus the old-language
interpretation of a general amalgam equals the concrete general
amalgam of the two reducts, including entire set-valued function
fibres.

The final induction carries an actual TreeAmalgamation certificate
through all its constructors, not merely a homomorphism from the
target into some arbitrary structure.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x} {X : Type y}

/-- Forgetting E commutes with Γ-relabeling of all original symbols. -/
theorem forgetFixedBinary_relabel
    (act : L.Action Γ) (g : Γ)
    (A : Structure L.withFixedBinaryRel V) :
    (A.relabel act.withFixedBinaryRel g).forgetFixedBinary =
      (A.forgetFixedBinary).relabel act g := by
  rfl

namespace Embedding

/-- The reduct preserves composites of genuine Γ-embeddings. -/
theorem forgetFixedBinary_comp
    (act : L.Action Γ)
    {A : Structure L.withFixedBinaryRel V}
    {B : Structure L.withFixedBinaryRel W}
    {C : Structure L.withFixedBinaryRel X}
    (g : Embedding act.withFixedBinaryRel B C)
    (f : Embedding act.withFixedBinaryRel A B) :
    (g.comp f).forgetFixedBinary act =
      (g.forgetFixedBinary act).comp (f.forgetFixedBinary act) := by
  rfl

end Embedding
end Structure

namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- The concrete general free amalgam commutes exactly with
forgetting E, without changing its quotient carrier. -/
theorem forgetFixedBinary_generalAmalgamStructure
    (act : L.Action Γ)
    {C : Structure L.withFixedBinaryRel I}
    {B₁ : Structure L.withFixedBinaryRel X}
    {B₂ : Structure L.withFixedBinaryRel Y}
    (f : Structure.Embedding act.withFixedBinaryRel C B₁)
    (g : Structure.Embedding act.withFixedBinaryRel C B₂) :
    (generalAmalgamStructure act.withFixedBinaryRel f g).forgetFixedBinary =
      generalAmalgamStructure act
        (f.forgetFixedBinary act) (g.forgetFixedBinary act) := by
  rfl

end TreeLike

namespace TreeLike

universe u v w
variable {L : Language.{u}} {Γ : Type w} [Group Γ]
variable {U : Type v}

/-- Literal trees of complete expanded full A copies remain literal tree
amalgamations of full reduct copies of A after deleting E. -/
theorem TreeAmalgamation.forgetFixedBinary
    (act : L.Action Γ)
    (A : Structure L.withFixedBinaryRel U)
    {V : Type v}
    (B : Structure L.withFixedBinaryRel V)
    (h : TreeAmalgamation act.withFixedBinaryRel A B) :
    TreeAmalgamation act A.forgetFixedBinary B.forgetFixedBinary := by
  induction h with
  | copy C f hsurj =>
      exact .copy C.forgetFixedBinary
        (f.forgetFixedBinary act) hsurj
  | glue C B₁ B₂ h₁ h₂ δ₁ δ₂ α₁ α₂ ih₁ ih₂ =>
      rw [forgetFixedBinary_generalAmalgamStructure]
      exact TreeAmalgamation.glue
        C.forgetFixedBinary B₁.forgetFixedBinary B₂.forgetFixedBinary
        ih₁ ih₂
        (δ₁.forgetFixedBinary act)
        (δ₂.forgetFixedBinary act)
        (α₁.forgetFixedBinary act)
        (α₂.forgetFixedBinary act)

end TreeLike
end AllThoseEPPA
