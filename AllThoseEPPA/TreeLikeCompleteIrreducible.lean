import AllThoseEPPA.TreeLikeClique

/-!
# Complete E-reducts are irreducible

In the induction for Lemma `lem:cuts`, a structure with a
complete distinguished E-reduct is already irreducible.
This is independent of finiteness and of the language's function
arities, and does not require the ambient structure to be faithful.

The proof is the elementary free-decomposition argument:
an E-clique cannot meet both exclusive sides of a free amalgam.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A complete simple E-reduct forces the whole structure to be
irreducible. -/
theorem edgeComplete_isIrreducible
    (B : Structure L V) (E : L.RelSymbol 2)
    (hComplete : B.EdgeComplete E) :
    B.IsIrreducible := by
  have hClique : EdgeClique B E Set.univ := by
    intro x y hx hy hne
    exact (hComplete x y).2 hne
  constructor
  intro d
  rcases edgeClique_subset_one_side
      B E d Set.univ hClique with hleft | hright
  · apply d.left_proper
    apply Set.eq_univ_of_forall
    intro x
    exact hleft (Set.mem_univ x)
  · apply d.right_proper
    apply Set.eq_univ_of_forall
    intro x
    exact hright (Set.mem_univ x)

/-- Conversely, if E is loopless and the graph is not complete,
there is a distinct nonedge, ready for the generic chordal
free-cut construction. -/
theorem exists_distinct_nonedge_of_not_complete
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hNotComplete : ¬ B.EdgeComplete E) :
    ∃ x y : V, x ≠ y ∧ ¬ B.Edge E x y := by
  classical
  by_contra h
  apply hNotComplete
  intro x y
  constructor
  · intro hxy
    intro heq
    subst y
    exact hloop x hxy
  · intro hne
    by_contra hno
    exact h ⟨x,y,hne,hno⟩

end TreeLike
end AllThoseEPPA
