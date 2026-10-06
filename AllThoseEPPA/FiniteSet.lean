import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sort
import Mathlib.Logic.Equiv.Fintype
import AllThoseEPPA.EPPA

/-!
# Coherent extension of partial permutations of finite ordered sets

This is the combinatorial core of Proposition 2.5 in the paper.  A partial
permutation is completed by matching the unused domain and range elements in
increasing order.
-/

namespace AllThoseEPPA

namespace PartialEquiv

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The unique increasing bijection between the complements of the source and
target of a partial equivalence on a finite linear order. -/
noncomputable def orderedComplementOrderIso (p : PartialEquiv α α) :
    {x : α // x ∉ p.source} ≃o {x : α // x ∉ p.target} := by
  classical
  have hst : Fintype.card p.source = Fintype.card p.target :=
    Fintype.card_congr p.toEquiv
  have hc :
      Fintype.card {x : α // x ∉ p.source} =
        Fintype.card {x : α // x ∉ p.target} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hst]
  exact
    (Fintype.orderIsoFinOfCardEq {x : α // x ∉ p.source} rfl).symm.trans
      (Fintype.orderIsoFinOfCardEq {x : α // x ∉ p.target} hc.symm)

/-- Extend a partial equivalence of a finite linear order to a permutation by
matching the complementary elements in increasing order. -/
noncomputable def orderedExtension (p : PartialEquiv α α) : Equiv.Perm α := by
  classical
  exact Equiv.subtypeCongr p.toEquiv p.orderedComplementOrderIso.toEquiv

theorem orderedExtension_apply_of_mem (p : PartialEquiv α α) {x : α}
    (hx : x ∈ p.source) :
    p.orderedExtension x = p x := by
  classical
  simp [orderedExtension, Equiv.subtypeCongr, hx]

theorem orderedExtension_apply_of_not_mem (p : PartialEquiv α α) {x : α}
    (hx : x ∉ p.source) :
    p.orderedExtension x =
      p.orderedComplementOrderIso ⟨x, hx⟩ := by
  classical
  simp [orderedExtension, Equiv.subtypeCongr, hx]

end PartialEquiv
end AllThoseEPPA
