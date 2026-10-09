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


/-- The distinguished first index of a bad cycle, independent of length. -/
def firstIndex (c : BadCycleSequence A E) : Fin c.length :=
  ⟨0, by
    have h := c.length_ge_four
    omega⟩

/-- The distinguished last index of a bad cycle. -/
def lastIndex (c : BadCycleSequence A E) : Fin c.length :=
  ⟨c.length - 1, by
    have h := c.length_ge_four
    omega⟩

def firstVertex (c : BadCycleSequence A E) : V :=
  c.vertex c.firstIndex

def lastVertex (c : BadCycleSequence A E) : V :=
  c.vertex c.lastIndex

theorem firstVertex_ne_lastVertex (c : BadCycleSequence A E) :
    c.firstVertex ≠ c.lastVertex := by
  intro h
  have hindex : c.firstIndex = c.lastIndex :=
    c.injective h
  have hval := congrArg Fin.val hindex
  have hk := c.length_ge_four
  dsimp [firstIndex, lastIndex] at hval
  omega

theorem first_last_not_linear (c : BadCycleSequence A E) :
    ¬ LinearAdjacent c.firstIndex c.lastIndex := by
  have hk := c.length_ge_four
  change ¬ ((c.lastIndex).val = (c.firstIndex).val + 1 ∨
    (c.firstIndex).val = (c.lastIndex).val + 1)
  dsimp [firstIndex, lastIndex]
  omega

theorem last_first_not_linear (c : BadCycleSequence A E) :
    ¬ LinearAdjacent c.lastIndex c.firstIndex := by
  intro h
  exact c.first_last_not_linear
    ((linearAdjacent_symm c.lastIndex c.firstIndex).1 h)

/-- The only cyclic edges which are not linearly consecutive are precisely
the unordered pair of the two endpoints of the displayed cycle sequence. -/
theorem wrapPair_iff_ends (c : BadCycleSequence A E) (x y : V) :
    c.WrapPair x y ↔
      (x = c.firstVertex ∧ y = c.lastVertex) ∨
      (x = c.lastVertex ∧ y = c.firstVertex) := by
  constructor
  · rintro ⟨i, j, hix, hjy, hcyc, hnlin⟩
    rcases cyclicAdjacent_cases i j hcyc with
        hstep | ⟨hi, hj⟩ | hstep | ⟨hj, hi⟩
    · exact False.elim (hnlin (Or.inl hstep))
    · right
      have hieq : i = c.lastIndex := by
        apply Fin.ext
        dsimp [lastIndex]
        omega
      have hjeq : j = c.firstIndex := by
        apply Fin.ext
        dsimp [firstIndex]
        omega
      constructor
      · calc
          x = c.vertex i := hix.symm
          _ = c.lastVertex := by rw [hieq]; rfl
      · calc
          y = c.vertex j := hjy.symm
          _ = c.firstVertex := by rw [hjeq]; rfl
    · exact False.elim (hnlin (Or.inr hstep))
    · left
      have hieq : i = c.firstIndex := by
        apply Fin.ext
        dsimp [firstIndex]
        omega
      have hjeq : j = c.lastIndex := by
        apply Fin.ext
        dsimp [lastIndex]
        omega
      constructor
      · calc
          x = c.vertex i := hix.symm
          _ = c.firstVertex := by rw [hieq]; rfl
      · calc
          y = c.vertex j := hjy.symm
          _ = c.lastVertex := by rw [hjeq]; rfl
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · refine ⟨c.firstIndex, c.lastIndex, hx.symm, hy.symm, ?_, ?_⟩
      · right
        change (c.firstIndex).val =
          ((c.lastIndex).val + 1) % c.length
        have hk := c.length_ge_four
        have hlen : (c.lastIndex).val + 1 = c.length := by
          dsimp [lastIndex]
          omega
        rw [hlen, Nat.mod_self]
        rfl
      · exact c.first_last_not_linear
    · refine ⟨c.lastIndex, c.firstIndex, hx.symm, hy.symm, ?_, ?_⟩
      · left
        change (c.firstIndex).val =
          ((c.lastIndex).val + 1) % c.length
        have hk := c.length_ge_four
        have hlen : (c.lastIndex).val + 1 = c.length := by
          dsimp [lastIndex]
          omega
        rw [hlen, Nat.mod_self]
        rfl
      · exact c.last_first_not_linear

/-- The two branches of the genericity condition are disjoint. -/
theorem nonWrapPair_not_wrap
    (c : BadCycleSequence A E) {x y : V}
    (hnw : c.NonWrapPair x y) :
    ¬ c.WrapPair x y := by
  intro hw
  rcases (c.wrapPair_iff_ends x y).mp hw with
      ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rcases hnw with ⟨i, j, hi, hj, _, hlin⟩
    have hieq : i = c.firstIndex :=
      c.injective (hi.trans hx)
    have hjeq : j = c.lastIndex :=
      c.injective (hj.trans hy)
    rw [hieq, hjeq] at hlin
    exact c.first_last_not_linear hlin
  · rcases hnw with ⟨i, j, hi, hj, _, hlin⟩
    have hieq : i = c.lastIndex :=
      c.injective (hi.trans hx)
    have hjeq : j = c.firstIndex :=
      c.injective (hj.trans hy)
    rw [hieq, hjeq] at hlin
    exact c.last_first_not_linear hlin

end BadCycleSequence
end Structure
end AllThoseEPPA
