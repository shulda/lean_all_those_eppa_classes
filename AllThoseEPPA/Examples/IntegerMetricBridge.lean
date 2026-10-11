import AllThoseEPPA.Examples.IntegerMetricBasic
import AllThoseEPPA.UnrestrictedFaithfulEPPA
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Fin.VecNotation

/-!
# Relational encoding of finite bounded integer metrics

For each D we use one binary symbol per *positive* distance
1,...,D. A symbol indexed by d : Fin D represents the length d.val+1.
Zero distance is represented by equality, not by a binary loop.

The language is purely relational; the group of symbol relabellings
is trivial. The encoding is parametric in D, including D = 0.

The later metric EPPA theorem will prove that its final relational
witness admits a canonical metric completion. The raw unrestricted
relational witness need not itself encode any metric.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Positive distance colours, indexed by their arity. -/
inductive RelSymbol (D : ℕ) : ℕ → Type
  | edge (d : Fin D) : RelSymbol D 2

/-- The metric language has no function symbols. -/
abbrev FuncSymbol (_ : ℕ) : Type := Empty

def language (D : ℕ) : Language where
  RelSymbol := RelSymbol D
  FuncSymbol := FuncSymbol
  relArity_pos := by
    intro n R
    cases R
    decide

instance (D : ℕ) : (language D).HasUnaryFunctions where
  arity_eq_one := by
    intro n F
    exact F.elim

def action (D : ℕ) : (language D).Action PUnit.{1} :=
  Language.Action.trivial (language D) PUnit.{1}

/-- Trivial language permutations fix every distance colour. -/
@[simp] theorem action_on_edge (D : ℕ) (g : PUnit.{1})
    (d : Fin D) :
    (action D).onRel g (RelSymbol.edge d) =
      RelSymbol.edge d := by
  rfl

/-- Encode each strictly positive metric distance as a binary
relation; the symbol with index d represents distance d+1. -/
def toStructure {V : Type u} {D : ℕ} (M : BoundedNatMetric D V) :
    Structure (language D) V where
  rel := by
    intro n R xs
    cases R with
    | edge d =>
      exact M.dist (xs 0) (xs 1) = d.val + 1
  func := by
    intro n F xs
    exact F.elim

@[simp] theorem toStructure_edge {V : Type u} {D : ℕ}
    (M : BoundedNatMetric D V) (d : Fin D) (xs : Fin 2 → V) :
    (toStructure M).rel (RelSymbol.edge d) xs ↔
      M.dist (xs 0) (xs 1) = d.val + 1 :=
  Iff.rfl

/-- Reversing endpoints preserves the encoded distance colour. -/
theorem toStructure_edge_symm {V : Type u} {D : ℕ}
    (M : BoundedNatMetric D V) (d : Fin D) (x y : V) :
    (toStructure M).rel (RelSymbol.edge d) ![x, y] ↔
      (toStructure M).rel (RelSymbol.edge d) ![y, x] := by
  change (M.dist x y = d.val + 1) ↔
    (M.dist y x = d.val + 1)
  rw [M.dist_symm x y]

/-- Every positive-colour edge joins two distinct points. -/
theorem toStructure_edge_ne {V : Type u} {D : ℕ}
    (M : BoundedNatMetric D V) (d : Fin D) {x y : V}
    (h : (toStructure M).rel (RelSymbol.edge d) ![x, y]) :
    x ≠ y := by
  intro hxy
  subst y
  have hdist : M.dist x x = d.val + 1 := h
  rw [M.dist_self] at hdist
  omega

/-- The original structure has a finite relabelling orbit
because its symbol group is trivial. -/
theorem finiteOrbit {V : Type u} {D : ℕ}
    (M : BoundedNatMetric D V) :
    (toStructure M).HasFiniteRelabelOrbit (action D) := by
  classical
  exact Set.finite_range
    (fun g : PUnit => (toStructure M).relabel (action D) g)

end Bridge
end IntegerMetric
end AllThoseEPPA
