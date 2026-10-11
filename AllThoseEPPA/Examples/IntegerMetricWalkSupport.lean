import AllThoseEPPA.Examples.IntegerMetricNoShortcuts
import Mathlib.Data.Finset.Card

/-!
# Small support of a metric shortcut

The no-shortcut theorem isolates the only way in which a prescribed
edge length can fail to survive shortest-path completion. This module
extracts its FINITE witness: a walk of weight less than d visits at
most d vertices, because all nontrivial step costs are positive
integers.

Thus, when an original edge of weight d ≤ D is shortened, the
violation is supported on at most D vertices, *independently of the
size of the ambient structure*. This exact quantitative step is
needed to apply the verified bounded-substructure clause of
the restricted/tree-like EPPA theorem.

No claim about the existence of a metric completion of the
resulting local substructure is made here; that is the next bridge.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

namespace Walk

/-- The set of vertices visited by a walk, including its endpoints. -/
noncomputable def support {V : Type u} [DecidableEq V]
    {x y : V} (p : Walk V x y) : Finset V :=
  match p with
  | .nil a => {a}
  | .step (x := a) _ tail => insert a tail.support

/-- A walk's starting vertex lies in its visited-vertex support. -/
theorem start_mem_support {V : Type u} [DecidableEq V]
    {x y : V} (p : Walk V x y) :
    x ∈ p.support := by
  cases p with
  | nil a => simp [support]
  | step h tail => simp [support]

/-- A walk's terminal vertex also lies in its support. -/
theorem end_mem_support {V : Type u} [DecidableEq V]
    {x y : V} (p : Walk V x y) :
    y ∈ p.support := by
  induction p with
  | nil a => simp [support]
  | step h tail ih =>
      exact Finset.mem_insert_of_mem ih

/-- The number of visited vertices is at most the number
of nontrivial steps plus one, even when vertices repeat. -/
theorem support_card_le_steps {V : Type u} [DecidableEq V]
    {x y : V} (p : Walk V x y) :
    p.support.card ≤ p.steps + 1 := by
  induction p with
  | nil a => simp [support, steps]
  | @step a b z h tail ih =>
      change (insert a tail.support).card ≤ (tail.steps + 1) + 1
      have hcard := Finset.card_insert_le a tail.support
      omega

/-- Combine the vertex bound with positivity of integer edge costs. -/
theorem support_card_le_weight_succ
    {D : ℕ} {V : Type u} [DecidableEq V]
    (C : SymmetricCost D V) {x y : V}
    (p : Walk V x y) :
    p.support.card ≤ p.weight C + 1 := by
  calc
    p.support.card ≤ p.steps + 1 := p.support_card_le_steps
    _ ≤ p.weight C + 1 := Nat.add_le_add_right
      (p.steps_le_weight C) 1

/-- A shortcut of length <d can involve at most d distinct vertices. -/
theorem support_card_le_of_shorter
    {D : ℕ} {V : Type u} [DecidableEq V]
    (C : SymmetricCost D V) {x y : V}
    (p : Walk V x y) {d : ℕ}
    (h : p.weight C < d) :
    p.support.card ≤ d := by
  have hs := p.support_card_le_steps
  have ht := p.steps_lt_of_weight_lt C h
  omega

/-- Any walk shortening a direct cost c(x,y) in a D-bounded
symmetric cost matrix lives on at most D vertices. -/
theorem support_card_le_diameter_of_shortcut
    {D : ℕ} {V : Type u} [DecidableEq V]
    (C : SymmetricCost D V) {x y : V}
    (p : Walk V x y)
    (h : p.weight C < C.cost x y) :
    p.support.card ≤ D := by
  exact (p.support_card_le_of_shorter C h).trans (C.cost_le x y)

end Walk
end IntegerMetric
end AllThoseEPPA
