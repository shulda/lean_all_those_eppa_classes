import Mathlib.Data.Set.Card
import AllThoseEPPA.TreeLikeInducedCycles
import AllThoseEPPA.TreeLikeFaithfulGraph

/-!
# Induction infrastructure for the chordal tree-amalgamation lemma

The paper proves `lem:cuts` by induction on the number of vertices.
A genuine free decomposition has two proper closed sides, so on a
finite carrier each induced side has strictly fewer vertices.
Moreover, absence of induced E-cycles and the simple-graph laws for E
are hereditary to every closed induced substructure.

These elementary formal facts are kept separate from the as-yet
unproved recursive tree-amalgamation construction.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Each side of a free decomposition has smaller cardinality than
the finite ambient structure. -/
theorem freeDecomposition_side_card_lt
    [Finite V] (B : Structure L V) (d : B.FreeDecomposition) :
    Nat.card d.left < Nat.card V ∧
      Nat.card d.right < Nat.card V := by
  constructor
  · simpa only [Nat.card_coe_set_eq] using
      (Set.ncard_lt_card d.left_proper)
  · simpa only [Nat.card_coe_set_eq] using
      (Set.ncard_lt_card d.right_proper)

/-- Every closed induced substructure inherits E-looplessness. -/
theorem induced_edgeLoopless
    (B : Structure L V) (E : L.RelSymbol 2)
    (S : Set V) (hS : B.IsClosed S)
    (hloop : B.EdgeLoopless E) :
    (B.induce S hS).EdgeLoopless E := by
  intro x hx
  apply hloop x.1
  change B.rel E (Subtype.val ∘ Structure.pairTuple x x) at hx
  rwa [Structure.pairTuple_map] at hx

/-- Every closed induced substructure inherits E-symmetry. -/
theorem induced_edgeSymmetric
    (B : Structure L V) (E : L.RelSymbol 2)
    (S : Set V) (hS : B.IsClosed S)
    (hsymm : B.EdgeSymmetric E) :
    (B.induce S hS).EdgeSymmetric E := by
  intro x y
  change B.rel E (Subtype.val ∘ Structure.pairTuple x y) ↔
    B.rel E (Subtype.val ∘ Structure.pairTuple y x)
  simp only [Structure.pairTuple_map]
  exact hsymm x.1 y.1

/-- The no-bad-induced-cycle property is hereditary to closed
induced substructures. -/
theorem induced_noBadCycles
    (B : Structure L V) (E : L.RelSymbol 2)
    (S : Set V) (hS : B.IsClosed S)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False) :
    ∀ c : Structure.BadCycleSequence (B.induce S hS) E, False := by
  intro c
  exact hNo (liftBadCycle B E S hS c)

end TreeLike
end AllThoseEPPA
