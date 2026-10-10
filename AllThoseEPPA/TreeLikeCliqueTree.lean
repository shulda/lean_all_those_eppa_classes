import Mathlib.Data.Set.Card
import AllThoseEPPA.TreeLikeInducedIrreducibles

/-!
# Chordal structures admit a recursive clique-tree certificate

This is the inductive structural core of the paper's `lem:cuts`.
A clique-tree certificate is built from E-complete pieces using
proper free amalgams over *closed irreducible* intersections.

The fundamental theorem below shows that every finite
unary-function structure with chordal E-reduct and clique
irreducibles admits such a certificate. The induction is on
the number of vertices, because each free-decomposition side
is a strict subset, and `TreeLikeInducedIrreducibles` supplies
the hereditary hypotheses.

This is not yet the theorem that B embeds into a tree amalgam
of full copies of the original structure A: identifying each
complete leaf with an embeddable irreducible A-substructure,
and constructing a compatible amalgam of full A-copies,
remain separate obligations.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}}

/-- A structural certificate that B can be obtained by iterated
proper free amalgamation of E-complete induced pieces, glued
over irreducible (hence legitimate) amalgamation bases. -/
inductive CliqueTree (E : L.RelSymbol 2) :
    {W : Type v} → Structure L W → Prop where
  | complete {W : Type v} (B : Structure L W)
      (hComplete : B.EdgeComplete E) :
      CliqueTree E B
  | free {W : Type v} (B : Structure L W)
      (d : B.FreeDecomposition)
      (hBase : ∃ hS : B.IsClosed (d.left ∩ d.right),
        (B.induce (d.left ∩ d.right) hS).IsIrreducible)
      (hLeft : CliqueTree E (B.induce d.left d.left_closed))
      (hRight : CliqueTree E (B.induce d.right d.right_closed)) :
      CliqueTree E B

/-- **Recursive chordal-cut theorem.**
A finite unary-function structure with a symmetric loopless
distinguished E-relation, no induced E-cycles of length at least
four, and clique irreducibles is built by iterated free amalgams
of E-complete pieces over irreducible amalgamation bases.

This proof does not assume any EPPA extension property: those
are used only later to identify the complete pieces with
images of substructures of the original input A. -/
theorem chordal_hasCliqueTree
    [L.HasUnaryFunctions]
    {V : Type v} [Finite V]
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False) :
    CliqueTree E B := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (W : Type v) [Finite W] (C : Structure L W),
      Nat.card W = n →
      IrreduciblesAreCliques C E →
      C.EdgeLoopless E →
      C.EdgeSymmetric E →
      (∀ c : Structure.BadCycleSequence C E, False) →
      CliqueTree E C
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W hFinite C hCard hCliques hLoop hSymm hCycles
      letI : Finite W := hFinite
      rcases edgeComplete_or_irreducible_free_cut
          C E hCliques hLoop hSymm hCycles with
        hComplete | ⟨S, hS, hIrrS, d, hInter⟩
      · exact .complete C hComplete
      · have hLeftProper :
            d.left ⊂ (Set.univ : Set W) :=
          Set.ssubset_univ.mpr d.left_proper
        have hRightProper :
            d.right ⊂ (Set.univ : Set W) :=
          Set.ssubset_univ.mpr d.right_proper
        have hLeftSmaller : Nat.card d.left < n := by
          have hlt :
              d.left.ncard < (Set.univ : Set W).ncard :=
            Set.ncard_lt_ncard hLeftProper
              (Set.toFinite (Set.univ : Set W))
          have hlt' : Nat.card d.left < Nat.card W := by
            simpa [Nat.card_coe_set_eq] using hlt
          exact hlt'.trans_eq hCard
        have hRightSmaller : Nat.card d.right < n := by
          have hlt :
              d.right.ncard < (Set.univ : Set W).ncard :=
            Set.ncard_lt_ncard hRightProper
              (Set.toFinite (Set.univ : Set W))
          have hlt' : Nat.card d.right < Nat.card W := by
            simpa [Nat.card_coe_set_eq] using hlt
          exact hlt'.trans_eq hCard
        have hLeft :
            CliqueTree E (C.induce d.left d.left_closed) :=
          ih (Nat.card d.left) hLeftSmaller
            d.left (C.induce d.left d.left_closed) rfl
            (irreduciblesAreCliques_induced
              C E hCliques d.left d.left_closed)
            (edgeLoopless_induced C E hLoop d.left d.left_closed)
            (edgeSymmetric_induced C E hSymm d.left d.left_closed)
            (noBadCycles_induced C E hCycles d.left d.left_closed)
        have hRight :
            CliqueTree E (C.induce d.right d.right_closed) :=
          ih (Nat.card d.right) hRightSmaller
            d.right (C.induce d.right d.right_closed) rfl
            (irreduciblesAreCliques_induced
              C E hCliques d.right d.right_closed)
            (edgeLoopless_induced C E hLoop d.right d.right_closed)
            (edgeSymmetric_induced C E hSymm d.right d.right_closed)
            (noBadCycles_induced C E hCycles d.right d.right_closed)
        have hBase :
            ∃ hClosed : C.IsClosed (d.left ∩ d.right),
              (C.induce (d.left ∩ d.right) hClosed).IsIrreducible := by
          have hClosed : C.IsClosed (d.left ∩ d.right) := by
            rw [hInter]
            exact hS
          refine ⟨hClosed, ?_⟩
          simpa only [hInter] using hIrrS
        exact .free C d hBase hLeft hRight
  exact hP (Nat.card V) V B rfl hIrred hloop hsymm hNo

end TreeLike
end AllThoseEPPA
