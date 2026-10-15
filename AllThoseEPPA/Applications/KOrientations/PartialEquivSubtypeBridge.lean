import Mathlib.Logic.Equiv.PartialEquiv
import AllThoseEPPA.PartialIso

/-!
# Partial equivalences from bijections of closed domains

A concrete bijection `e : s ≃ t` between two vertex subsets of the
same ambient carrier determines a partial equivalence with exactly
those source and target sets. Outside its source or target the
underlying total maps take arbitrary irrelevant values (here the
identity fallback).

This generic adapter is needed when a first-stage graph
automorphism induces an auxiliary root partial isomorphism.
Using `PartialEquiv.EqOnSource` rather than raw equality avoids
coherence constraints on the irrelevant outside-domain values.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Build a genuine partial equivalence from any bijection between
two subtypes of the same carrier, even when one domain is empty. -/
noncomputable def partialEquivFromSubtypeEquiv
    {X : Type u} (s t : Set X) (e : s ≃ t) :
    PartialEquiv X X where
  toFun := fun x =>
    if hx : x ∈ s then (e ⟨x, hx⟩).val else x
  invFun := fun y =>
    if hy : y ∈ t then (e.symm ⟨y, hy⟩).val else y
  source := s
  target := t
  map_source' := by
    intro x hx
    change (if hh : x ∈ s then (e ⟨x, hh⟩).val else x) ∈ t
    simp only [dif_pos hx]
    exact (e ⟨x, hx⟩).property
  map_target' := by
    intro y hy
    change (if hh : y ∈ t then (e.symm ⟨y, hh⟩).val else y) ∈ s
    simp only [dif_pos hy]
    exact (e.symm ⟨y, hy⟩).property
  left_inv' := by
    intro x hx
    have hy : (e ⟨x, hx⟩).val ∈ t := (e ⟨x, hx⟩).property
    change
      (if hh : (if h : x ∈ s then (e ⟨x, h⟩).val else x) ∈ t
       then (e.symm
         ⟨(if h : x ∈ s then (e ⟨x, h⟩).val else x), hh⟩).val
       else (if h : x ∈ s then (e ⟨x, h⟩).val else x)) = x
    simp only [dif_pos hx, dif_pos hy]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  right_inv' := by
    intro y hy
    have hx : (e.symm ⟨y, hy⟩).val ∈ s :=
      (e.symm ⟨y, hy⟩).property
    change
      (if hh : (if h : y ∈ t then (e.symm ⟨y, h⟩).val else y) ∈ s
       then (e
         ⟨(if h : y ∈ t then (e.symm ⟨y, h⟩).val else y), hh⟩).val
       else (if h : y ∈ t then (e.symm ⟨y, h⟩).val else y)) = y
    simp only [dif_pos hy, dif_pos hx]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)

/-- On its source, the partial map really is the original e. -/
theorem partialEquivFromSubtypeEquiv_apply
    {X : Type u} (s t : Set X) (e : s ≃ t)
    {x : X} (hx : x ∈ s) :
    partialEquivFromSubtypeEquiv s t e x = (e ⟨x, hx⟩).val := by
  simp [partialEquivFromSubtypeEquiv, dif_pos hx]

/-- Its source and target are exactly the prescribed closed domains. -/
theorem partialEquivFromSubtypeEquiv_source_target
    {X : Type u} (s t : Set X) (e : s ≃ t) :
    (partialEquivFromSubtypeEquiv s t e).source = s ∧
    (partialEquivFromSubtypeEquiv s t e).target = t := by
  exact ⟨rfl, rfl⟩

end AllThoseEPPA.Applications.KOrientations
