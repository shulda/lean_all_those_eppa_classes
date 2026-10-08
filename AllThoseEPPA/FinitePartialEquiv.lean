import AllThoseEPPA.FiniteSet

/-!
# Coherent completion of heterogeneous finite partial equivalences

The faithful EPPA construction needs to complete partial bijections between
different finite label types of the same cardinality.  This file generalizes
the order-preserving completion from `FiniteSet.lean`.
-/

namespace AllThoseEPPA
namespace PartialEquiv

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The increasing bijection between complements for a partial equivalence
between two finite linearly ordered types of equal cardinality. -/
noncomputable def orderedComplementOrderIsoOfCardEq
    [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β]
    (p : PartialEquiv α β)
    (hcard : Fintype.card α = Fintype.card β) :
    {x : α // x ∉ p.source} ≃o {y : β // y ∉ p.target} := by
  classical
  have hst :
      Fintype.card p.source = Fintype.card p.target :=
    Fintype.card_congr p.toEquiv
  have hc :
      Fintype.card {x : α // x ∉ p.source} =
        Fintype.card {y : β // y ∉ p.target} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl,
      hst, hcard]
  exact
    (Fintype.orderIsoFinOfCardEq
      {x : α // x ∉ p.source} rfl).symm.trans
      (Fintype.orderIsoFinOfCardEq
        {y : β // y ∉ p.target} hc.symm)

/-- Extend a partial equivalence between two finite linearly ordered types of
equal cardinality by matching complements increasingly. -/
noncomputable def orderedExtensionOfCardEq
    [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β]
    (p : PartialEquiv α β)
    (hcard : Fintype.card α = Fintype.card β) :
    α ≃ β := by
  classical
  let c := orderedComplementOrderIsoOfCardEq p hcard
  refine
    { toFun := fun x =>
        if hx : x ∈ p.source then p x else c ⟨x, hx⟩
      invFun := fun y =>
        if hy : y ∈ p.target then p.symm y else c.symm ⟨y, hy⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    by_cases hx : x ∈ p.source
    · have hpx : p x ∈ p.target := p.map_source hx
      simp [hx, hpx, p.left_inv hx]
    · have hc :
          ((c ⟨x, hx⟩ : {y : β // y ∉ p.target}) : β) ∉
            p.target :=
        (c ⟨x, hx⟩).property
      simp [hx, hc, c]
  · intro y
    by_cases hy : y ∈ p.target
    · have hpy : p.symm y ∈ p.source := p.map_target hy
      simp [hy, hpy, p.right_inv hy]
    · have hc :
          ((c.symm ⟨y, hy⟩ :
            {x : α // x ∉ p.source}) : α) ∉ p.source :=
        (c.symm ⟨y, hy⟩).property
      simp [hy, hc, c]

theorem orderedExtensionOfCardEq_apply_of_mem
    [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β]
    (p : PartialEquiv α β)
    (hcard : Fintype.card α = Fintype.card β)
    {x : α} (hx : x ∈ p.source) :
    orderedExtensionOfCardEq p hcard x = p x := by
  classical
  simp [orderedExtensionOfCardEq, hx]

theorem orderedExtensionOfCardEq_apply_of_not_mem
    [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β]
    (p : PartialEquiv α β)
    (hcard : Fintype.card α = Fintype.card β)
    {x : α} (hx : x ∉ p.source) :
    orderedExtensionOfCardEq p hcard x =
      orderedComplementOrderIsoOfCardEq p hcard ⟨x, hx⟩ := by
  classical
  simp [orderedExtensionOfCardEq, hx]

/-- Heterogeneous order-preserving completion is coherent under composition. -/
theorem orderedExtensionOfCardEq_trans'
    [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β]
    [Fintype γ] [LinearOrder γ]
    (p : PartialEquiv α β)
    (q : PartialEquiv β γ)
    (ht : p.target = q.source)
    (hαβ : Fintype.card α = Fintype.card β)
    (hβγ : Fintype.card β = Fintype.card γ)
    (hαγ : Fintype.card α = Fintype.card γ) :
    orderedExtensionOfCardEq (p.trans' q ht) hαγ =
      (orderedExtensionOfCardEq p hαβ).trans
        (orderedExtensionOfCardEq q hβγ) := by
  classical
  ext x
  by_cases hx : x ∈ p.source
  · have hqx : p x ∈ q.source := by
      rw [← ht]
      exact p.map_source hx
    rw [orderedExtensionOfCardEq_apply_of_mem
      (p.trans' q ht) hαγ hx]
    rw [Equiv.trans_apply,
      orderedExtensionOfCardEq_apply_of_mem p hαβ hx,
      orderedExtensionOfCardEq_apply_of_mem q hβγ hqx]
    rfl
  · have hcomp :
        {y : β | y ∉ p.target} =
          {y : β | y ∉ q.source} := by
      ext y
      simp [ht]
    let bridge :
        {y : β // y ∉ p.target} ≃o
          {y : β // y ∉ q.source} :=
      Set.orderIsoOfEq _ _ hcomp
    let e :
        {x : α // x ∉ p.source} ≃o
          {z : γ // z ∉ q.target} :=
      (orderedComplementOrderIsoOfCardEq p hαβ).trans
        (bridge.trans
          (orderedComplementOrderIsoOfCardEq q hβγ))
    have he :
        e =
          orderedComplementOrderIsoOfCardEq
            (p.trans' q ht) hαγ :=
      Subsingleton.elim _ _
    have hy :
        ((orderedComplementOrderIsoOfCardEq p hαβ
            ⟨x, hx⟩ :
          {y : β // y ∉ p.target}) : β) ∉ q.source := by
      rw [← ht]
      exact
        (orderedComplementOrderIsoOfCardEq p hαβ
          ⟨x, hx⟩).property
    rw [orderedExtensionOfCardEq_apply_of_not_mem
      (p.trans' q ht) hαγ hx]
    rw [Equiv.trans_apply,
      orderedExtensionOfCardEq_apply_of_not_mem p hαβ hx,
      orderedExtensionOfCardEq_apply_of_not_mem q hβγ hy]
    rw [← he]
    change
      (orderedComplementOrderIsoOfCardEq q hβγ
        (bridge
          (orderedComplementOrderIsoOfCardEq p hαβ
            ⟨x, hx⟩)) : γ) =
      (orderedComplementOrderIsoOfCardEq q hβγ
        ⟨(orderedComplementOrderIsoOfCardEq p hαβ
            ⟨x, hx⟩ : β), hy⟩ : γ)
    congr 1

end PartialEquiv
end AllThoseEPPA
