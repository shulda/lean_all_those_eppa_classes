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


/-- The canonical total extension sends the source of a partial equivalence
exactly onto its target. -/
theorem orderedExtension_mem_target_iff (p : PartialEquiv α α) (x : α) :
    orderedExtension p x ∈ p.target ↔ x ∈ p.source := by
  classical
  by_cases hx : x ∈ p.source
  · constructor
    · intro _
      exact hx
    · intro _
      rw [orderedExtension_apply_of_mem p hx]
      exact p.map_source hx
  · constructor
    · intro ht
      rw [orderedExtension_apply_of_not_mem p hx] at ht
      exact ((orderedComplementOrderIso p ⟨x, hx⟩).property ht).elim
    · intro hs
      exact (hx hs).elim


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
    rw [← he]
    change
      (orderedComplementOrderIso q
          (bridge (orderedComplementOrderIso p ⟨x, hx⟩)) : α) =
        (orderedComplementOrderIso q
          ⟨(orderedComplementOrderIso p ⟨x, hx⟩ : α), hy⟩ : α)
    congr 1

/-- The canonical ordered extension depends only on the mathematical partial
map, not on the irrelevant values of a `PartialEquiv` outside its source. -/
theorem orderedExtension_eq_of_eqOnSource {p q : PartialEquiv α α}
    (hpq : PartialEquiv.EqOnSource p q) :
    orderedExtension p = orderedExtension q := by
  classical
  ext x
  by_cases hx : x ∈ p.source
  · have hxq : x ∈ q.source := by
      rw [← hpq.1]
      exact hx
    rw [orderedExtension_apply_of_mem p hx,
      orderedExtension_apply_of_mem q hxq]
    exact hpq.2 hx
  · have hxq : x ∉ q.source := by
      intro hxq
      exact hx (hpq.1 ▸ hxq)
    rw [orderedExtension_apply_of_not_mem p hx,
      orderedExtension_apply_of_not_mem q hxq]
    have hs :
        {x : α | x ∉ p.source} = {x : α | x ∉ q.source} := by
      rw [hpq.1]
    have ht0 : p.target = q.target :=
      PartialEquiv.EqOnSource.target_eq hpq
    have ht :
        {x : α | x ∉ p.target} = {x : α | x ∉ q.target} := by
      rw [ht0]
    let sourceBridge :
        {x : α // x ∉ p.source} ≃o {x : α // x ∉ q.source} :=
      Set.orderIsoOfEq _ _ hs
    let targetBridge :
        {x : α // x ∉ p.target} ≃o {x : α // x ∉ q.target} :=
      Set.orderIsoOfEq _ _ ht
    let leftIso :
        {x : α // x ∉ p.source} ≃o {x : α // x ∉ q.target} :=
      (orderedComplementOrderIso p).trans targetBridge
    let rightIso :
        {x : α // x ∉ p.source} ≃o {x : α // x ∉ q.target} :=
      sourceBridge.trans (orderedComplementOrderIso q)
    have he : leftIso = rightIso :=
      Subsingleton.elim _ _
    have happ := congrArg (fun e' => (e' ⟨x, hx⟩ : α)) he
    change
      (targetBridge (orderedComplementOrderIso p ⟨x, hx⟩) : α) =
        (orderedComplementOrderIso q (sourceBridge ⟨x, hx⟩) : α) at happ
    calc
      (orderedComplementOrderIso p ⟨x, hx⟩ : α) =
          (targetBridge (orderedComplementOrderIso p ⟨x, hx⟩) : α) := by
        rfl
      _ = (orderedComplementOrderIso q (sourceBridge ⟨x, hx⟩) : α) :=
        happ
      _ = (orderedComplementOrderIso q ⟨x, hxq⟩ : α) := by
        congr 1

end PartialEquiv

/-- **Finite sets have coherent EPPA (explicit form).**

For every finite set there is a simultaneous choice of extensions of all
partial permutations to permutations.  It extends each partial permutation,
depends only on the mathematical partial map, and respects every defined
composition.  This is the Lean counterpart of Proposition
`prop:setcoherence` in the paper.

A linear order is chosen internally only to define the canonical extension;
it is not part of the statement. -/
theorem finiteSetsHaveCoherentEPPA (α : Type*) [Fintype α] :
    ∃ extension : PartialEquiv α α → Equiv.Perm α,
      (∀ (p : PartialEquiv α α) (x : α),
        x ∈ p.source → extension p x = p x) ∧
      (∀ (p q : PartialEquiv α α),
        PartialEquiv.EqOnSource p q → extension p = extension q) ∧
      ∀ (p q : PartialEquiv α α) (h : p.target = q.source),
        extension (p.trans' q h) =
          (extension p).trans (extension q) := by
  classical
  letI : LinearOrder α :=
    LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  refine ⟨PartialEquiv.orderedExtension, ?_⟩
  constructor
  · intro p x hx
    exact PartialEquiv.orderedExtension_apply_of_mem p hx
  constructor
  · intro p q hpq
    exact PartialEquiv.orderedExtension_eq_of_eqOnSource hpq
  · intro p q h
    exact PartialEquiv.orderedExtension_trans' p q h

end AllThoseEPPA
