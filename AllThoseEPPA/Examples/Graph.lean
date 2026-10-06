import Mathlib.Algebra.Group.PUnit
import Mathlib.Combinatorics.SimpleGraph.Basic
import AllThoseEPPA.EPPA

/-!
# Simple graphs as AllThoseEPPA structures

This file is the specialization bridge for the warm-up graph construction in
Section 3 of the paper.
-/

namespace AllThoseEPPA
namespace Graph

/-- The graph language has one binary relation symbol. -/
inductive RelSymbol : ℕ → Type
  | edge : RelSymbol 2

/-- No function symbols occur in the graph language. -/
abbrev FuncSymbol (_ : ℕ) : Type := Empty

/-- The language of simple graphs. -/
def language : Language where
  RelSymbol := RelSymbol
  FuncSymbol := FuncSymbol

/-- Graphs use the trivial language-permutation group. -/
def action : language.Action PUnit :=
  Language.Action.trivial language PUnit

/-- Regard a mathlib simple graph as a structure in the graph language. -/
def toStructure {V : Type*} (G : SimpleGraph V) :
    Structure language V where
  rel := by
    intro n R x
    cases R with
    | edge => exact G.Adj (x 0) (x 1)
  func := by
    intro n F x
    exact Empty.elim F

@[simp] theorem toStructure_edge {V : Type*} (G : SimpleGraph V)
    (x : Fin 2 → V) :
    (toStructure G).rel RelSymbol.edge x ↔ G.Adj (x 0) (x 1) :=
  Iff.rfl

end Graph
end AllThoseEPPA
