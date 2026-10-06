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
  exact Equiv.subtypeCongr p.toEquiv (orderedComplementOrderIso p).toEquiv

theorem orderedExtension_apply_of_mem (p : PartialEquiv α α) {x : α}
    (hx : x ∈ p.source) :
    orderedExtension p x = p x := by
  classical
  simp [orderedExtension, Equiv.subtypeCongr, hx, PartialEquiv.toEquiv]

theorem orderedExtension_apply_of_not_mem (p : PartialEquiv α α) {x : α}
    (hx : x ∉ p.source) :
    orderedExtension p x =
      orderedComplementOrderIso p ⟨x, hx⟩ := by
  classical
  simp [orderedExtension, Equiv.subtypeCongr, hx]


/-- The order-preserving extension is coherent under composition whenever the
range of the first partial equivalence is exactly the domain of the second. -/
theorem orderedExtension_trans' (p q : PartialEquiv α α)
    (h : p.target = q.source) :
    orderedExtension (p.trans' q h) =
      (orderedExtension p).trans (orderedExtension q) := by
  classical
  ext x
  by_cases hx : x ∈ p.source
  · have hqx : p x ∈ q.source := by
      rw [← h]
      exact p.map_source hx
    rw [orderedExtension_apply_of_mem (p.trans' q h) hx]
    rw [Equiv.trans_apply, orderedExtension_apply_of_mem p hx,
      orderedExtension_apply_of_mem q hqx]
    rfl
  · have hcomp :
        {x : α | x ∉ p.target} = {x : α | x ∉ q.source} := by
      ext y
      simp [h]
    let bridge :
        {x : α // x ∉ p.target} ≃o {x : α // x ∉ q.source} :=
      Set.orderIsoOfEq _ _ hcomp
    let e :
        {x : α // x ∉ p.source} ≃o {x : α // x ∉ q.target} :=
      (orderedComplementOrderIso p).trans
        (bridge.trans (orderedComplementOrderIso q))
    have he :
        e = orderedComplementOrderIso (p.trans' q h) :=
      Subsingleton.elim _ _
    have hy :
        ((orderedComplementOrderIso p ⟨x, hx⟩ : {y : α // y ∉ p.target}) : α)
          ∉ q.source := by
      rw [← h]
      exact (orderedComplementOrderIso p ⟨x, hx⟩).property
    rw [orderedExtension_apply_of_not_mem (p.trans' q h) hx]
    rw [Equiv.trans_apply, orderedExtension_apply_of_not_mem p hx,
      orderedExtension_apply_of_not_mem q hy]
    have happ := congrArg (fun e' => (e' ⟨x, hx⟩ : α)) he
    simpa [e, bridge, Set.orderIsoOfEq_apply] using happ.symm

end PartialEquiv
end AllThoseEPPA
