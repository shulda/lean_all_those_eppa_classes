import Lean.Elab.Tactic.Omega
import AllThoseEPPA.CycleSparseningTheorem

/-!
# Counting the number of sparsening stages

This is the finite descent argument in the proof of Theorem `thm:maintree`.
The cycle-sparsening trichotomy is applied repeatedly to the successive
images of a chosen small substructure. Either a stage has no induced
distinguished cycle, or the vertex count increases when travelling from the
old witness to the new witness, or its edge count strictly decreases.

We use a general edge budget `Q` rather than the binomial coefficient in
the paper. This is intentional: `Sparsening.EdgePairs` counts **ordered**
edges, so the convenient uniform bound on a subset of at most `n`
vertices is `n * n`, not `n.choose 2`. A larger iteration count is
harmless for the restricted EPPA theorem.
-/

namespace AllThoseEPPA
namespace TreeLike

/-- Lexicographic rank, with the vertex count as the primary coordinate
and the *deficit* in the edge count as the secondary coordinate. -/
def sparseningRank (Q vertices edges : ℕ) : ℕ :=
  (vertices - 1) * (Q + 1) + (Q - edges)

/-- The rank is always strictly less than the number of available
vertex/edge states. -/
theorem sparseningRank_lt_budget
    (n Q vertices edges : ℕ)
    (hpos : 1 ≤ vertices)
    (hv : vertices ≤ n)
    (he : edges ≤ Q) :
    sparseningRank Q vertices edges < n * (Q + 1) := by
  have hmul :
      (vertices - 1 + 1) * (Q + 1) ≤ n * (Q + 1) :=
    Nat.mul_le_mul_right (Q + 1) (by omega : vertices - 1 + 1 ≤ n)
  have hstep :
      (vertices - 1) * (Q + 1) + (Q + 1) ≤ n * (Q + 1) := by
    simpa [Nat.add_mul] using hmul
  unfold sparseningRank
  omega

/-- Increasing the vertex count strictly increases the rank,
regardless of how the edge count changes within its budget. -/
theorem sparseningRank_lt_of_vertices_lt
    (Q v w e f : ℕ)
    (hpos : 1 ≤ v)
    (hv : v < w)
    (he : e ≤ Q)
    (hf : f ≤ Q) :
    sparseningRank Q v e < sparseningRank Q w f := by
  have hmul :
      (v - 1 + 1) * (Q + 1) ≤ (w - 1) * (Q + 1) :=
    Nat.mul_le_mul_right (Q + 1) (by omega : v - 1 + 1 ≤ w - 1)
  have hstep :
      (v - 1) * (Q + 1) + (Q + 1) ≤ (w - 1) * (Q + 1) := by
    simpa [Nat.add_mul] using hmul
  unfold sparseningRank
  omega

/-- With unchanged vertex count, a strict edge-count decrease
strictly increases the rank. -/
theorem sparseningRank_lt_of_edges_lt
    (Q v e f : ℕ)
    (he : e ≤ Q)
    (hf : f ≤ Q)
    (hfe : f < e) :
    sparseningRank Q v e < sparseningRank Q v f := by
  unfold sparseningRank
  omega

/-- Any of the two non-good alternatives of the sparsening
trichotomy strictly increases the rank. -/
theorem sparseningRank_lt_of_progress
    (Q v w e f : ℕ)
    (hpos : 1 ≤ v)
    (hvw : v ≤ w)
    (he : e ≤ Q)
    (hf : f ≤ Q)
    (hprogress : v < w ∨ f < e) :
    sparseningRank Q v e < sparseningRank Q w f := by
  by_cases hv : v < w
  · exact sparseningRank_lt_of_vertices_lt Q v w e f hpos hv he hf
  · have hveq : v = w := by omega
    subst w
    rcases hprogress with h | h
    · omega
    · exact sparseningRank_lt_of_edges_lt Q v e f he hf h

/-- **Finite-descent lemma for the restricted EPPA construction.**

There are `n * (Q+1)` sparsening steps and `n * (Q+1)+1`
structures, indexed in chronological order. At each stage the vertex
count is nondecreasing, all vertex counts are between 1 and `n`,
and all directed-edge counts are at most `Q`.

If each step satisfies the abstract sparsening trichotomy, some
resulting stage must satisfy its good alternative. In applications,
`good (i+1)` says that the chosen substructure of stage `i+1`
contains no induced E-cycle of length at least four. -/
theorem exists_good_sparsening_step
    (n Q : ℕ) (vertices edges : ℕ → ℕ) (good : ℕ → Prop)
    (hpos : ∀ i ≤ n * (Q + 1), 1 ≤ vertices i)
    (hvertices : ∀ i ≤ n * (Q + 1), vertices i ≤ n)
    (hedges : ∀ i ≤ n * (Q + 1), edges i ≤ Q)
    (hmono : ∀ i < n * (Q + 1), vertices i ≤ vertices (i + 1))
    (htrich : ∀ i < n * (Q + 1),
      good (i + 1) ∨
      vertices i < vertices (i + 1) ∨
      edges (i + 1) < edges i) :
    ∃ i < n * (Q + 1), good (i + 1) := by
  by_contra hnone
  have hprogress (i : ℕ) (hi : i < n * (Q + 1)) :
      vertices i < vertices (i + 1) ∨
      edges (i + 1) < edges i := by
    rcases htrich i hi with hg | hv | he
    · exact False.elim (hnone ⟨i, hi, hg⟩)
    · exact Or.inl hv
    · exact Or.inr he
  have hrank (i : ℕ) (hi : i ≤ n * (Q + 1)) :
      i ≤ sparseningRank Q (vertices i) (edges i) := by
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hlt : i < n * (Q + 1) := by omega
      have hprev : i ≤ n * (Q + 1) := by omega
      have hrise :=
        sparseningRank_lt_of_progress Q
          (vertices i) (vertices (i + 1)) (edges i) (edges (i + 1))
          (hpos i hprev) (hmono i hlt)
          (hedges i hprev) (hedges (i + 1) (by omega))
          (hprogress i hlt)
      have hprevRank := ih hprev
      omega
  have hfinal :=
    hrank (n * (Q + 1)) (le_refl _)
  have hbound :=
    sparseningRank_lt_budget n Q
      (vertices (n * (Q + 1))) (edges (n * (Q + 1)))
      (hpos _ (le_refl _))
      (hvertices _ (le_refl _))
      (hedges _ (le_refl _))
  omega

end TreeLike
end AllThoseEPPA
