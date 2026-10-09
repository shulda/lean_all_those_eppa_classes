import AllThoseEPPA.TreeLikeClique
import AllThoseEPPA.UnaryFunctions

/-!
# Graph separators yield genuine free decompositions

This is the second, function-sensitive ingredient of the
chordal-cut Lemma `lem:cuts`. Suppose all irreducible substructures
are cliques for a distinguished symmetric binary relation E.
Then a graph cut whose separator is *closed under the functions*
is automatically a free-amalgamation cut of the entire structure.

In particular:
* relation tuples cannot straddle its exclusive sides (the
  closure of every realized relation tuple is irreducible);
* each exclusive side is closed under unary functions (the closure
  of a point is irreducible);
* tuples of inputs to unary functions cannot straddle the cut.

This lemma is independent of the chordal-graph argument that will
produce the relevant clique separator.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}

/-- A closed separator with no E-edges between its two exclusive
sides gives a free decomposition of the entire structure.
The distinguished E must be symmetric; no completeness or
looplessness assumption is needed at this stage. -/
theorem freeDecomposition_of_closed_edge_separator
    (B : Structure L V) (E : L.RelSymbol 2)
    (hIrred : IrreduciblesAreCliques B E)
    (hSymm : B.EdgeSymmetric E)
    (X Y : Set V)
    (hcover : X ∪ Y = Set.univ)
    (hinter : B.IsClosed (X ∩ Y))
    (hcross : ∀ (x : V), x ∈ X → x ∉ Y →
      ∀ (y : V), y ∈ Y → y ∉ X → ¬ B.Edge E x y)
    (hXproper : X ≠ Set.univ) (hYproper : Y ≠ Set.univ) :
    B.FreeDecomposition := by
  classical
  have hclosedX : B.IsClosed X := by
    intro n F xs hxs z hz
    let i := UnaryFunctions.unaryIndex F
    let x := xs i
    have hx : x ∈ X := hxs i
    have htuple : xs = fun _ => x :=
      UnaryFunctions.unaryTuple_eq_constant F xs
    by_cases hxY : x ∈ Y
    · have hall : ∀ j, xs j ∈ X ∩ Y := by
        intro j
        have hj : xs j = x := congrFun htuple j
        rw [hj]
        exact ⟨hx, hxY⟩
      exact (hinter F xs hall hz).1
    · by_contra hzNotX
      have hzY : z ∈ Y := by
        have hmem : z ∈ X ∪ Y := by
          rw [hcover]
          exact Set.mem_univ z
        rcases hmem with hzX | hzY
        · exact (hzNotX hzX).elim
        · exact hzY
      have hneq : x ≠ z := by
        intro heq
        subst z
        exact hzNotX hx
      have hfib : z ∈ B.func F (fun _ => x) := by
        rw [htuple] at hz
        exact hz
      have hedge : B.Edge E x z :=
        function_value_edge B E hIrred F x z hfib hneq
      exact (hcross x hx hxY z hzY hzNotX) hedge
  have hclosedY : B.IsClosed Y := by
    intro n F xs hxs z hz
    let i := UnaryFunctions.unaryIndex F
    let x := xs i
    have hx : x ∈ Y := hxs i
    have htuple : xs = fun _ => x :=
      UnaryFunctions.unaryTuple_eq_constant F xs
    by_cases hxX : x ∈ X
    · have hall : ∀ j, xs j ∈ X ∩ Y := by
        intro j
        have hj : xs j = x := congrFun htuple j
        rw [hj]
        exact ⟨hxX, hx⟩
      exact (hinter F xs hall hz).2
    · by_contra hzNotY
      have hzX : z ∈ X := by
        have hmem : z ∈ X ∪ Y := by
          rw [hcover]
          exact Set.mem_univ z
        rcases hmem with hzX | hzY
        · exact hzX
        · exact (hzNotY hzY).elim
      have hneq : x ≠ z := by
        intro heq
        subst z
        exact hzNotY hx
      have hfib : z ∈ B.func F (fun _ => x) := by
        rw [htuple] at hz
        exact hz
      have hedge : B.Edge E x z :=
        function_value_edge B E hIrred F x z hfib hneq
      have hreverse : B.Edge E z x := (hSymm x z).mp hedge
      exact (hcross z hzX hzNotY x hx hxX) hreverse
  refine
    { left := X
      right := Y
      left_closed := hclosedX
      right_closed := hclosedY
      cover := hcover
      left_proper := hXproper
      right_proper := hYproper
      rel_local := ?_
      func_cross_empty := ?_ }
  · intro n R xs hrel
    by_cases hX : ∀ i, xs i ∈ X
    · exact Or.inl hX
    by_cases hY : ∀ i, xs i ∈ Y
    · exact Or.inr hY
    exfalso
    obtain ⟨i, hi⟩ := not_forall.mp hX
    obtain ⟨j, hj⟩ := not_forall.mp hY
    have hiY : xs i ∈ Y := by
      have hmem : xs i ∈ X ∪ Y := by
        rw [hcover]
        exact Set.mem_univ (xs i)
      rcases hmem with h | h
      · exact (hi h).elim
      · exact h
    have hjX : xs j ∈ X := by
      have hmem : xs j ∈ X ∪ Y := by
        rw [hcover]
        exact Set.mem_univ (xs j)
      rcases hmem with h | h
      · exact h
      · exact (hj h).elim
    have hne : xs j ≠ xs i := by
      intro heq
      exact hi (heq ▸ hjX)
    have hedge : B.Edge E (xs j) (xs i) :=
      relation_tuple_edge B E hIrred R xs hrel j i hne
    exact (hcross (xs j) hjX hj (xs i) hiY hi) hedge
  · intro n F xs hcrossTuple
    exfalso
    apply hcrossTuple
    have htuple : xs = fun _ => xs (UnaryFunctions.unaryIndex F) :=
      UnaryFunctions.unaryTuple_eq_constant F xs
    have hx : xs (UnaryFunctions.unaryIndex F) ∈ X ∪ Y := by
      rw [hcover]
      exact Set.mem_univ _
    rcases hx with hxX | hxY
    · left
      intro j
      rw [congrFun htuple j]
      exact hxX
    · right
      intro j
      rw [congrFun htuple j]
      exact hxY

end TreeLike
end AllThoseEPPA
