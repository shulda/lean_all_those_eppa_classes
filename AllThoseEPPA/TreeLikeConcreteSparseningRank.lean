import AllThoseEPPA.TreeLikeEdgeBudget
import AllThoseEPPA.CycleSparseningTrichotomy

/-!
# A concrete sparsening step increases the bounded rank

The paper's proof of `thm:maintree` iterates cycle sparsening.
`TreeLikeDescent` already proves a purely numerical pigeonhole
theorem: if the number of projected vertices is nondecreasing
and, at each step, one of two measures strictly improves, then
one of the finitely many stages must have no induced E-cycle.

Here we plug the **actual** sparsening trichotomy into that rank:
given a nonempty subset S of the *new* sparsening witness,
either S contains no long induced E-cycle, or the rank of its
projection into the *old* witness is strictly smaller than the
rank of S. The bound on E-edges is n*n because `EdgePairs`
counts **ordered** pairs, not unordered graph edges.

This statement handles all vertex subsets, not just closed
substructures; closure is supplied later when iterating the
projections of a chosen small substructure.

No artificial additional cycle or genericity assumption is made.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {V : Type v} [Finite V]

/-- Concrete one-step rank alternative for cycle sparsening:
for any nonempty subset S of the new witness with at most n
vertices, either S has no long induced E-cycle, or the bounded
(vertex-count, directed-edge-deficit) rank **strictly increases**
from its projected vertex set in the old structure to S.

This combines `Sparsening.sparsening_trichotomy`,
`edgePairs_card_le_budget` and
`sparseningRank_lt_of_progress`, and is designed to
be iterated across a tower of finite EPPA witnesses. -/
theorem concrete_sparsening_rank_progress
    (B : Structure L V) (E : L.RelSymbol 2)
    (S : Set (Sparsening.WitnessVertex B E))
    (n : ℕ)
    (hNonempty : S.Nonempty)
    (hBound : S.ncard ≤ n) :
    ¬ Sparsening.ContainsInducedCycle B E S ∨
      sparseningRank (n * n)
        (Set.image (fun w => w.base B E) S).ncard
        (Nat.card (Sparsening.EdgePairs B E
          (Set.image (fun w => w.base B E) S))) <
      sparseningRank (n * n)
        S.ncard
        (Nat.card (Sparsening.EdgePairs
          (Sparsening.witnessStructure B E) E S)) := by
  classical
  letI : Finite (Sparsening.WitnessVertex B E) :=
    Sparsening.witnessVertex_finite B E
  let T : Set V := Set.image (fun w => w.base B E) S
  have hFiniteS : S.Finite := Set.toFinite S
  have hOldPos : 1 ≤ T.ncard := by
    have hT : T.Nonempty := by
      obtain ⟨x, hx⟩ := hNonempty
      exact ⟨x.base B E, ⟨x, hx, rfl⟩⟩
    exact (Set.ncard_pos (Set.toFinite T)).mpr hT
  have hMono : T.ncard ≤ S.ncard :=
    Set.ncard_image_le hFiniteS
  have hEdgesOld :
      Nat.card (Sparsening.EdgePairs B E T) ≤ n * n :=
    edgePairs_card_le_budget B E T n (hMono.trans hBound)
  have hEdgesNew :
      Nat.card (Sparsening.EdgePairs
        (Sparsening.witnessStructure B E) E S) ≤ n * n :=
    edgePairs_card_le_budget
      (Sparsening.witnessStructure B E) E S n hBound
  rcases Sparsening.sparsening_trichotomy B E S with hNo | hInc | hDec
  · exact Or.inl hNo
  · right
    exact sparseningRank_lt_of_progress (n * n)
      T.ncard S.ncard
      (Nat.card (Sparsening.EdgePairs B E T))
      (Nat.card (Sparsening.EdgePairs
        (Sparsening.witnessStructure B E) E S))
      hOldPos hMono hEdgesOld hEdgesNew (Or.inl hInc)
  · right
    exact sparseningRank_lt_of_progress (n * n)
      T.ncard S.ncard
      (Nat.card (Sparsening.EdgePairs B E T))
      (Nat.card (Sparsening.EdgePairs
        (Sparsening.witnessStructure B E) E S))
      hOldPos hMono hEdgesOld hEdgesNew (Or.inr hDec)

end TreeLike
end AllThoseEPPA
