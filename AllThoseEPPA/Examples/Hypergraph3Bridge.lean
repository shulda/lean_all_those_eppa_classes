import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import AllThoseEPPA.UnrestrictedFaithfulEPPA
import AllThoseEPPA.Examples.Hypergraph3Basic

/-!
Internal bridge between ordinary set-based 3-uniform hypergraphs and the
relational language of the general irreducible-faithful EPPA theorem.

The public theorem is in Hypergraph3.lean; these definitions deliberately
do not occur in its statement.
-/

namespace Hypergraph3
namespace Bridge

open AllThoseEPPA

universe u v

inductive RelSymbol : ℕ → Type
  | triple : RelSymbol 3

abbrev FuncSymbol (_ : ℕ) : Type := Empty

def language : Language where
  RelSymbol := RelSymbol
  FuncSymbol := FuncSymbol
  relArity_pos := by
    intro n R
    cases R
    decide

instance : language.HasUnaryFunctions where
  arity_eq_one := by
    intro n F
    exact F.elim

def action : language.Action PUnit.{0} :=
  Language.Action.trivial language PUnit.{0}

/-- The only ternary symbol is fixed by the language action. -/
@[simp] theorem action_on_triple (g : PUnit.{0}) :
    action.onRel g RelSymbol.triple = RelSymbol.triple := by
  rfl

/-- Encode an unordered triple as one ternary relation. -/
def toStructure {V : Type*} (A : Hypergraph3 V) :
    AllThoseEPPA.Structure language V where
  rel := by
    intro n R xs
    cases R with
    | triple => exact A.edge (Set.range xs)
  func := by
    intro n F xs
    exact F.elim

@[simp] theorem toStructure_triple {V : Type*}
    (A : Hypergraph3 V) (xs : Fin 3 → V) :
    (toStructure A).rel RelSymbol.triple xs ↔
      A.edge (Set.range xs) :=
  Iff.rfl

theorem range_triple {V : Type*} (xs : Fin 3 → V) :
    Set.range xs = {xs 0, xs 1, xs 2} := by
  classical
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩

/-- Only the one trivial language relabelling is possible. -/
theorem finiteOrbit {V : Type*} (A : Hypergraph3 V) :
    (toStructure A).HasFiniteRelabelOrbit action := by
  classical
  exact Set.finite_range (fun g : PUnit => (toStructure A).relabel action g)

/-- Turn an actual bijection between two subsets into the library's partial
equivalence. Values off the domain and range are irrelevant. -/
noncomputable def partialEquiv {V : Type*}
    (U W : Set V) (p : U ≃ W) : PartialEquiv V V := by
  classical
  exact {
    toFun x := if hx : x ∈ U then (p ⟨x, hx⟩).1 else x
    invFun y := if hy : y ∈ W then (p.symm ⟨y, hy⟩).1 else y
    source := U
    target := W
    map_source' := by
      intro x hx
      simp [hx]
    map_target' := by
      intro y hy
      simp [hy]
    left_inv' := by
      intro x hx
      simp [hx]
    right_inv' := by
      intro y hy
      simp [hy]
  }

@[simp] theorem partialEquiv_apply_of_mem {V : Type*}
    {U W : Set V} (p : U ≃ W) {x : V} (hx : x ∈ U) :
    partialEquiv U W p x = (p ⟨x, hx⟩).1 := by
  simp [partialEquiv, hx]


/-- The partial isomorphism induced by an edge-preserving bijection of
two induced subhypergraphs. -/
noncomputable def partialAutomorphism {V : Type*}
    (A : Hypergraph3 V) (U W : Set V) (p : U ≃ W)
    (hp : ∀ a b c : U,
      A.edge {a.1, b.1, c.1} ↔
        A.edge {(p a).1, (p b).1, (p c).1}) :
    AllThoseEPPA.Structure.PartialAutomorphism action (toStructure A) where
  lang := 1
  toPartialEquiv := partialEquiv U W p
  source_closed := by
    intro n F xs hxs y hy
    exact F.elim
  target_closed := by
    intro n F xs hxs y hy
    exact F.elim
  map_rel_iff := by
    intro n R xs hxs
    cases R with
    | triple =>
      have hx0 : xs 0 ∈ U := hxs 0
      have hx1 : xs 1 ∈ U := hxs 1
      have hx2 : xs 2 ∈ U := hxs 2
      have he :=
        (hp ⟨xs 0, hx0⟩ ⟨xs 1, hx1⟩ ⟨xs 2, hx2⟩).symm
      change
        A.edge (Set.range (partialEquiv U W p ∘ xs)) ↔
          A.edge (Set.range xs)
      rw [range_triple, range_triple]
      simpa only [Function.comp_apply,
        partialEquiv_apply_of_mem p hx0,
        partialEquiv_apply_of_mem p hx1,
        partialEquiv_apply_of_mem p hx2] using he
  map_func := by
    intro n F xs hxs
    exact F.elim

end Bridge
end Hypergraph3
