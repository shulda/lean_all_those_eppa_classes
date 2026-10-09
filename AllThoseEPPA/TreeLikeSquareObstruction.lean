import Mathlib.Tactic.FinCases
import AllThoseEPPA.TreeLikeInducedCycles

/-!
# The four-cycle obstruction in the chordal-cut proof

This is the first explicit graph obstruction needed by the proof of
`lem:cuts`. Two nonadjacent vertices x,y joined via two different
mutually nonadjacent common neighbours a,b span an induced 4-cycle.
The result is stated directly using `Structure.BadCycleSequence`,
the notion of forbidden induced cycle already used in `lem:sparsen`.

In particular, for a chordal E-reduct this configuration is impossible.
The longer-path version is still needed to show that every minimal
vertex separator is a clique.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The cyclic ordering of the four vertices x,a,y,b. -/
def squareVertex (x a y b : V) (i : Fin 4) : V :=
  if i = 0 then x else
  if i = 1 then a else
  if i = 2 then y else b

/-- Six inequalities are exactly what is needed for the tuple
of the four vertices to be injective. -/
theorem squareVertex_injective
    (x a y b : V)
    (hxa : x ≠ a) (hxy : x ≠ y) (hxb : x ≠ b)
    (hay : a ≠ y) (hab : a ≠ b) (hyb : y ≠ b) :
    Function.Injective (squareVertex x a y b) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [squareVertex]

/-- Four distinct vertices with the required four edges and the
two missing chords form a bad induced E-cycle of length four. -/
def badCycleOfInducedSquare
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (x a y b : V)
    (hxa : x ≠ a) (hxy : x ≠ y) (hxb : x ≠ b)
    (hay : a ≠ y) (hab : a ≠ b) (hyb : y ≠ b)
    (heXA : B.Edge E x a)
    (heAY : B.Edge E a y)
    (heYB : B.Edge E y b)
    (heBX : B.Edge E b x)
    (hnoXY : ¬ B.Edge E x y)
    (hnoAB : ¬ B.Edge E a b) :
    Structure.BadCycleSequence B E := by
  have heAX : B.Edge E a x := (hsymm x a).mp heXA
  have heYA : B.Edge E y a := (hsymm a y).mp heAY
  have heBY : B.Edge E b y := (hsymm y b).mp heYB
  have heXB : B.Edge E x b := (hsymm b x).mp heBX
  have hnoYX : ¬ B.Edge E y x := by
    intro h
    exact hnoXY ((hsymm x y).mpr h)
  have hnoBA : ¬ B.Edge E b a := by
    intro h
    exact hnoAB ((hsymm a b).mpr h)
  have hnoXX : ¬ B.Edge E x x := hloop x
  have hnoAA : ¬ B.Edge E a a := hloop a
  have hnoYY : ¬ B.Edge E y y := hloop y
  have hnoBB : ¬ B.Edge E b b := hloop b
  refine
    { length := 4
      length_ge_four := by omega
      vertex := squareVertex x a y b
      injective := squareVertex_injective x a y b
        hxa hxy hxb hay hab hyb
      edge_iff := ?_ }
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [squareVertex, Structure.CyclicAdjacent,
      Structure.CyclicSuccessor, heXA, heAY, heYB, heBX,
      heAX, heYA, heBY, heXB,
      hnoXY, hnoYX, hnoAB, hnoBA,
      hnoXX, hnoAA, hnoYY, hnoBB]

/-- In a graph without induced cycles of length at least four,
two nonadjacent vertices cannot have two nonadjacent common
neighbours, provided the four vertices are distinct. -/
theorem no_induced_square_of_no_bad_cycles
    (B : Structure L V) (E : L.RelSymbol 2)
    (hloop : B.EdgeLoopless E)
    (hsymm : B.EdgeSymmetric E)
    (hNo : ∀ c : Structure.BadCycleSequence B E, False)
    (x a y b : V)
    (hxa : x ≠ a) (hxy : x ≠ y) (hxb : x ≠ b)
    (hay : a ≠ y) (hab : a ≠ b) (hyb : y ≠ b)
    (heXA : B.Edge E x a)
    (heAY : B.Edge E a y)
    (heYB : B.Edge E y b)
    (heBX : B.Edge E b x)
    (hnoXY : ¬ B.Edge E x y)
    (hnoAB : ¬ B.Edge E a b) : False :=
  hNo (badCycleOfInducedSquare B E hloop hsymm x a y b
    hxa hxy hxb hay hab hyb heXA heAY heYB heBX
    hnoXY hnoAB)

end TreeLike
end AllThoseEPPA
