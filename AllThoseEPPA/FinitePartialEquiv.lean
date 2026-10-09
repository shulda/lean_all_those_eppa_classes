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

/-- The heterogeneous canonical ordered extension depends only on the
mathematical partial map, not on irrelevant values outside its source. -/
theorem orderedExtensionOfCardEq_eq_of_eqOnSource
    [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β]
    {p q : PartialEquiv α β}
    (hcard : Fintype.card α = Fintype.card β)
    (hpq : PartialEquiv.EqOnSource p q) :
    orderedExtensionOfCardEq p hcard =
      orderedExtensionOfCardEq q hcard := by
  classical
  ext x
  by_cases hx : x ∈ p.source
  · have hxq : x ∈ q.source := by
      rw [← hpq.1]
      exact hx
    rw [orderedExtensionOfCardEq_apply_of_mem p hcard hx,
      orderedExtensionOfCardEq_apply_of_mem q hcard hxq]
    exact hpq.2 hx
  · have hxq : x ∉ q.source := by
      intro hxq
      exact hx (hpq.1 ▸ hxq)
    rw [orderedExtensionOfCardEq_apply_of_not_mem p hcard hx,
      orderedExtensionOfCardEq_apply_of_not_mem q hcard hxq]
    have hs :
        {x : α | x ∉ p.source} =
          {x : α | x ∉ q.source} := by
      rw [hpq.1]
    have ht0 : p.target = q.target :=
      PartialEquiv.EqOnSource.target_eq hpq
    have ht :
        {y : β | y ∉ p.target} =
          {y : β | y ∉ q.target} := by
      rw [ht0]
    let sourceBridge :
        {x : α // x ∉ p.source} ≃o
          {x : α // x ∉ q.source} :=
      Set.orderIsoOfEq _ _ hs
    let targetBridge :
        {y : β // y ∉ p.target} ≃o
          {y : β // y ∉ q.target} :=
      Set.orderIsoOfEq _ _ ht
    let leftIso :
        {x : α // x ∉ p.source} ≃o
          {y : β // y ∉ q.target} :=
      (orderedComplementOrderIsoOfCardEq p hcard).trans
        targetBridge
    let rightIso :
        {x : α // x ∉ p.source} ≃o
          {y : β // y ∉ q.target} :=
      sourceBridge.trans
        (orderedComplementOrderIsoOfCardEq q hcard)
    have he : leftIso = rightIso :=
      Subsingleton.elim _ _
    have happ :=
      congrArg (fun e' => (e' ⟨x, hx⟩ : β)) he
    change
      (targetBridge
          (orderedComplementOrderIsoOfCardEq p hcard
            ⟨x, hx⟩) : β) =
        (orderedComplementOrderIsoOfCardEq q hcard
          (sourceBridge ⟨x, hx⟩) : β) at happ
    calc
      (orderedComplementOrderIsoOfCardEq p hcard
          ⟨x, hx⟩ : β) =
          (targetBridge
            (orderedComplementOrderIsoOfCardEq p hcard
              ⟨x, hx⟩) : β) := by
        rfl
      _ =
          (orderedComplementOrderIsoOfCardEq q hcard
            (sourceBridge ⟨x, hx⟩) : β) := happ
      _ =
          (orderedComplementOrderIsoOfCardEq q hcard
            ⟨x, hxq⟩ : β) := by
        congr 1

/-- Canonical ordered completion is natural under an order isomorphism of
the codomain, provided the two partial equivalences have the same source and
agree there after applying the order isomorphism. -/
theorem orderedExtensionOfCardEq_natural
    [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β]
    [Fintype γ] [LinearOrder γ]
    (p : PartialEquiv α β)
    (q : PartialEquiv α γ)
    (e : β ≃o γ)
    (hαβ : Fintype.card α = Fintype.card β)
    (hαγ : Fintype.card α = Fintype.card γ)
    (hs : p.source = q.source)
    (hmap : ∀ x, x ∈ p.source → e (p x) = q x) :
    (orderedExtensionOfCardEq p hαβ).trans e.toEquiv =
      orderedExtensionOfCardEq q hαγ := by
  classical
  have htarget : ∀ y : β, e y ∈ q.target ↔ y ∈ p.target := by
    intro y
    constructor
    · intro hey
      let x : α := q.symm (e y)
      have hxq : x ∈ q.source := q.map_target hey
      have hxp : x ∈ p.source := by
        rw [hs]
        exact hxq
      have hqy : q x = e y := q.right_inv hey
      have heq : e (p x) = e y :=
        (hmap x hxp).trans hqy
      have hpx : p x = y := e.injective heq
      have hpt : p x ∈ p.target := p.map_source hxp
      simpa [hpx] using hpt
    · intro hy
      let x : α := p.symm y
      have hxp : x ∈ p.source := p.map_target hy
      have hxq : x ∈ q.source := by
        rw [← hs]
        exact hxp
      have hpy : p x = y := p.right_inv hy
      have hqt : q x ∈ q.target := q.map_source hxq
      have hqx : q x = e y := by
        calc
          q x = e (p x) := (hmap x hxp).symm
          _ = e y := congrArg e hpy
      simpa [hqx] using hqt
  have hsCompl :
      {x : α | x ∉ p.source} =
        {x : α | x ∉ q.source} := by
    rw [hs]
  let sourceBridge :
      {x : α // x ∉ p.source} ≃o
        {x : α // x ∉ q.source} :=
    Set.orderIsoOfEq _ _ hsCompl
  let targetBridge :
      {y : β // y ∉ p.target} ≃o
        {z : γ // z ∉ q.target} :=
    { toEquiv :=
        { toFun := fun y =>
            ⟨e y.1, by
              intro hy
              exact y.2 ((htarget y.1).1 hy)⟩
          invFun := fun z =>
            ⟨e.symm z.1, by
              intro hy
              apply z.2
              have hmem :
                  e (e.symm z.1) ∈ q.target :=
                (htarget (e.symm z.1)).2 hy
              simpa using hmem⟩
          left_inv := by
            intro y
            apply Subtype.ext
            simp
          right_inv := by
            intro z
            apply Subtype.ext
            simp }
      map_rel_iff' := by
        intro y z
        change e y.1 ≤ e z.1 ↔ y.1 ≤ z.1
        exact e.le_iff_le }
  ext x
  by_cases hx : x ∈ p.source
  · have hxq : x ∈ q.source := by
      rw [← hs]
      exact hx
    rw [Equiv.trans_apply,
      orderedExtensionOfCardEq_apply_of_mem p hαβ hx,
      orderedExtensionOfCardEq_apply_of_mem q hαγ hxq]
    exact hmap x hx
  · have hxq : x ∉ q.source := by
      intro hxq
      apply hx
      rw [hs]
      exact hxq
    rw [Equiv.trans_apply,
      orderedExtensionOfCardEq_apply_of_not_mem p hαβ hx,
      orderedExtensionOfCardEq_apply_of_not_mem q hαγ hxq]
    let leftIso :
        {x : α // x ∉ p.source} ≃o
          {z : γ // z ∉ q.target} :=
      (orderedComplementOrderIsoOfCardEq p hαβ).trans
        targetBridge
    let rightIso :
        {x : α // x ∉ p.source} ≃o
          {z : γ // z ∉ q.target} :=
      sourceBridge.trans
        (orderedComplementOrderIsoOfCardEq q hαγ)
    have he : leftIso = rightIso :=
      Subsingleton.elim _ _
    have happ :=
      congrArg (fun e' => (e' ⟨x, hx⟩ : γ)) he
    change
      (targetBridge
          (orderedComplementOrderIsoOfCardEq p hαβ
            ⟨x, hx⟩) : γ) =
        (orderedComplementOrderIsoOfCardEq q hαγ
          (sourceBridge ⟨x, hx⟩) : γ) at happ
    calc
      e (orderedComplementOrderIsoOfCardEq p hαβ
          ⟨x, hx⟩ : β) =
          (targetBridge
            (orderedComplementOrderIsoOfCardEq p hαβ
              ⟨x, hx⟩) : γ) := by
        rfl
      _ =
          (orderedComplementOrderIsoOfCardEq q hαγ
            (sourceBridge ⟨x, hx⟩) : γ) := happ
      _ =
          (orderedComplementOrderIsoOfCardEq q hαγ
            ⟨x, hxq⟩ : γ) := by
        congr 1

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
