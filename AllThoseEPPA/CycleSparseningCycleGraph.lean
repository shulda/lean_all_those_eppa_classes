import Lean.Elab.Tactic.Omega
import AllThoseEPPA.CycleSparseningIrreducible

/-!
# Triangle-freeness of bad induced cycle sequences

A bad cycle has length at least four.  The three pairwise-adjacency
conditions cannot hold simultaneously, even if some indices coincide.
This elementary index fact is used to show that a bad cycle intersects
a complete distinguished copy in at most two vertices.
-/

namespace AllThoseEPPA
namespace Structure

/-- A directed successor on a finite cycle is either an ordinary
consecutive pair or the last-to-first wrap. -/
theorem cyclicSuccessor_cases {k : ℕ} (i j : Fin k)
    (h : CyclicSuccessor i j) :
    j.val = i.val + 1 ∨
      (i.val + 1 = k ∧ j.val = 0) := by
  change j.val = (i.val + 1) % k at h
  by_cases hi : i.val + 1 < k
  · left
    simpa [Nat.mod_eq_of_lt hi] using h
  · right
    have he : i.val + 1 = k := by
      have := i.isLt
      omega
    rw [he, Nat.mod_self] at h
    exact ⟨he, h⟩

/-- Expand a cyclic adjacency into its four possible oriented/index cases. -/
theorem cyclicAdjacent_cases {k : ℕ} (i j : Fin k)
    (h : CyclicAdjacent i j) :
    j.val = i.val + 1 ∨
      (i.val + 1 = k ∧ j.val = 0) ∨
      i.val = j.val + 1 ∨
      (j.val + 1 = k ∧ i.val = 0) := by
  rcases h with h | h
  · rcases cyclicSuccessor_cases i j h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases cyclicSuccessor_cases j i h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- The cyclic adjacency relation on a cycle of length at least four is
triangle-free.  This is deliberately a standalone arithmetic lemma. -/
theorem cyclicAdjacent_no_triangle {k : ℕ} (hk : 4 ≤ k)
    (i j l : Fin k)
    (hij : CyclicAdjacent i j)
    (hjl : CyclicAdjacent j l)
    (hli : CyclicAdjacent l i) : False := by
  have hi := i.isLt
  have hj := j.isLt
  have hl := l.isLt
  rcases cyclicAdjacent_cases i j hij with h1 | h1 | h1 | h1 <;>
    rcases cyclicAdjacent_cases j l hjl with h2 | h2 | h2 | h2 <;>
    rcases cyclicAdjacent_cases l i hli with h3 | h3 | h3 | h3 <;>
    omega

namespace BadCycleSequence

variable {L : Language} {V : Type*}
variable {A : Structure L V} {E : L.RelSymbol 2}

/-- No three vertices of a bad induced cycle are pairwise connected by E. -/
theorem no_edge_triangle
    (c : BadCycleSequence A E)
    (i j l : Fin c.length)
    (hij : A.Edge E (c.vertex i) (c.vertex j))
    (hjl : A.Edge E (c.vertex j) (c.vertex l))
    (hli : A.Edge E (c.vertex l) (c.vertex i)) : False :=
  cyclicAdjacent_no_triangle c.length_ge_four i j l
    ((c.edge_iff i j).1 hij)
    ((c.edge_iff j l).1 hjl)
    ((c.edge_iff l i).1 hli)

end BadCycleSequence
end Structure
end AllThoseEPPA
