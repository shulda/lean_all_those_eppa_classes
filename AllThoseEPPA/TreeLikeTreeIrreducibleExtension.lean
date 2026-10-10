import AllThoseEPPA.TreeLikeFullAAmalgamation
import AllThoseEPPA.TreeLikeGeneralAmalgamFreeCover
import AllThoseEPPA.TreeLikeIrreducibleExtensionLift

/-!
# Irreducible substructures extend to an A-copy in a tree amalgamation

This is the precise extension part of Observation
`obs:tree-amalgamation_irreducible` in the manuscript.

For *any* recursive tree amalgamation of genuine full copies
of A, every closed irreducible induced substructure sits
inside the image of some exact Γ-embedding of the whole A.

The proof inducts on the actual recursive tree construction.
The base copy is surjective. At a glue step, the general
free-cover lemma first localizes the irreducible substructure
inside **one** source side (also for degenerate attachments and
different language permutations). The previously checked
extension-lifting theorem then moves the IH's A-copy through
that side's exact Γ-embedding into the new amalgam.

No finiteness or unary-function restrictions are needed for
this structural observation. This is not yet `lem:cuts`: the
separate task is to *embed arbitrary chordal B* into such a
tree-of-A-copies.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} {Γ : Type w} [Group Γ]
variable {U : Type v}

/-- Every closed irreducible induced substructure of a genuine
tree amalgamation of full A-copies extends to an actual embedded
whole copy of A. This is the paper's
`obs:tree-amalgamation_irreducible` extension statement. -/
theorem TreeAmalgamation.everyIrreducibleExtendsToA
    (act : L.Action Γ) (A : Structure L U)
    {V : Type v} {H : Structure L V}
    (h : TreeAmalgamation act A H) :
    EveryIrreducibleExtendsToA act A H := by
  induction h with
  | copy C f hSurj =>
      intro S hS hIrr
      refine ⟨f, ?_⟩
      intro x hx
      exact hSurj x
  | glue C B₁ B₂ h₁ h₂ δ₁ δ₂ α₁ α₂ ih₁ ih₂ =>
      intro S hS hIrr
      let f : Structure.Embedding act C B₁ := α₁.comp δ₁
      let g : Structure.Embedding act C B₂ := α₂.comp δ₂
      rcases generalAmalgam_irreducible_in_side
          act f g S hS hIrr with hLeft | hRight
      · exact extendIrreducible_throughEmbeddedSide
          act A B₁ (generalAmalgamStructure act f g)
          (generalAmalgamLeftEmbedding act f g)
          ih₁ S hS hIrr hLeft
      · exact extendIrreducible_throughEmbeddedSide
          act A B₂ (generalAmalgamStructure act f g)
          (generalAmalgamRightEmbedding act f g)
          ih₂ S hS hIrr hRight

end TreeLike
end AllThoseEPPA
