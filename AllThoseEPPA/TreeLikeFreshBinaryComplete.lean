import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import AllThoseEPPA.CycleSparseningBasics
import AllThoseEPPA.TreeLikeFreshBinaryStructure

/-!
# The new E is a genuinely fixed, complete simple graph

The arbitrary-language reduction of manuscript thm:maintree
requires the *fresh* relation E to satisfy precisely the two
hypotheses used throughout the concrete sparsening tower:
the Γ-action fixes E, and E is a complete loopless graph
on the expanded input A. Both statements are proved here
from the explicit language action and structure expansion,
with no changes to the old language's relation symbols.
-/

namespace AllThoseEPPA

namespace Language

universe u v
variable {L : Language.{u}} {Γ : Type v} [Group Γ]

/-- Every Γ-permutation fixes the adjoined binary symbol,
not merely its particular interpretation in one structure. -/
theorem Action.withFixedBinaryRel_fixesFresh
    (act : L.Action Γ) :
    (act.withFixedBinaryRel).FixesRel
      (withFixedBinaryRel.freshE L) := by
  intro g
  exact Action.withFixedBinaryRel_onFresh act g

end Language

namespace Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The fresh E interpretation is literally the complete
loopless graph: the two vertices of a binary tuple are
E-related if and only if they are distinct. -/
theorem withCompleteFixedBinary_edgeComplete
    (A : Structure L V) :
    A.withCompleteFixedBinary.EdgeComplete
      (Language.withFixedBinaryRel.freshE L) := by
  intro x y
  change Function.Injective (pairTuple x y) ↔ x ≠ y
  constructor
  · intro hinj hxy
    have heq : (0 : Fin 2) = 1 :=
      hinj (by simp [pairTuple, hxy])
    exact (by decide : (0 : Fin 2) ≠ 1) heq
  · intro hne i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pairTuple]

end Structure
end AllThoseEPPA
