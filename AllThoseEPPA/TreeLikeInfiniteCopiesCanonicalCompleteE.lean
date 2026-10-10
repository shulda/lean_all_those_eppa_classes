import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import AllThoseEPPA.TreeLikeFreshBinaryComplete

/-!
# Every complete fresh E-relation is the canonical expansion

The manuscript's Lemma lem:infinitecopies states its result
for *any* expanded Γ-structure A⁺ with complete fresh E.
The preliminary formal statement uses the canonical
`A⁻.withCompleteFixedBinary` expansion.

These two presentations are identical, not merely
isomorphic: the fresh relation E is required to hold
precisely on pairs of distinct vertices; all old
relations and all set-valued function fibres are
unchanged by the canonical reduct/expansion.

This module proves the literal equality, enabling the
fully general original lemma statement without changing
a carrier, a Γ-action, or any recursive tree certificate.
-/

namespace AllThoseEPPA
namespace Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Over arity two, complete E is equivalent to injectivity
of its full tuple (including all tuples with repeated vertices). -/
theorem freshE_relation_iff_injective
    (A : Structure L.withFixedBinaryRel V)
    (hE : A.EdgeComplete (Language.withFixedBinaryRel.freshE L))
    (xs : Fin 2 → V) :
    A.rel (Language.withFixedBinaryRel.freshE L) xs ↔
      Function.Injective xs := by
  have htuple : pairTuple (xs 0) (xs 1) = xs := by
    funext i
    fin_cases i <;> rfl
  have hinj :
      Function.Injective (pairTuple (xs 0) (xs 1)) ↔
        xs 0 ≠ xs 1 := by
    constructor
    · intro h hxy
      have heq : (0 : Fin 2) = 1 :=
        h (by simp [pairTuple, hxy])
      exact (by decide : (0 : Fin 2) ≠ 1) heq
    · intro hxy i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [pairTuple]
  rw [← htuple]
  exact (hE (xs 0) (xs 1)).trans hinj.symm

/-- If E is interpreted as the complete loopless graph,
forgetting and canonically reintroducing it gives *exactly*
the original expanded Γ-structure, with no isomorphism or
language relabelling required. -/
theorem withCompleteFixedBinary_eq_of_edgeComplete
    (A : Structure L.withFixedBinaryRel V)
    (hE : A.EdgeComplete (Language.withFixedBinaryRel.freshE L)) :
    A.forgetFixedBinary.withCompleteFixedBinary = A := by
  have hRel :
      (A.forgetFixedBinary.withCompleteFixedBinary).rel = A.rel := by
    funext n R xs
    cases R with
    | inl r =>
        rfl
    | inr e =>
        have hn : n = 2 := e.2
        subst n
        have he : e = ⟨PUnit.unit, rfl⟩ :=
          Subsingleton.elim _ _
        subst e
        apply propext
        exact (freshE_relation_iff_injective A hE xs).symm
  have hFunc :
      (A.forgetFixedBinary.withCompleteFixedBinary).func = A.func := rfl
  exact congrArg₂
    (fun rel func => (Structure.mk rel func : Structure L.withFixedBinaryRel V))
    hRel hFunc

end Structure
end AllThoseEPPA
