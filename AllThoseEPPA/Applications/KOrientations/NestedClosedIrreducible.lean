import AllThoseEPPA.Irreducible

/-!
# Irreducible closed subsets inside reducible closed structures

Suppose U and T are closed in the same ambient set-valued-function
structure, with T ⊆ U. If U admits a free decomposition, but the
substructure induced on T is irreducible, then T lies entirely in
one side of that free decomposition.

This is the exact nested-closed-substructure variant of
Structure.irreducible_subset_one_side. It avoids transporting
IsIrreducible through two different nested Subtype carrier types:
a putative decomposition meeting T on both sides is pulled back
directly to T, contradicting irreducibility.

The helper is language-agnostic and will be applied to each
canonical root support inside the trace of a reconstructed d-piece.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

theorem irreducible_closed_subset_one_side_of_freeDecomposition
    {L : Language.{u}} {V : Type v}
    (A : Structure L V)
    (U T : Set V)
    (hU : A.IsClosed U) (hT : A.IsClosed T)
    (hTU : T ⊆ U)
    (d : (A.induce U hU).FreeDecomposition)
    (hIrr : (A.induce T hT).IsIrreducible) :
    T ⊆ Subtype.val '' d.left ∨
      T ⊆ Subtype.val '' d.right := by
  by_contra hNo
  have hNotLeft : ¬ T ⊆ Subtype.val '' d.left := by
    intro h
    exact hNo (Or.inl h)
  have hNotRight : ¬ T ⊆ Subtype.val '' d.right := by
    intro h
    exact hNo (Or.inr h)
  let leftT : Set T :=
    {t | (⟨t.val, hTU t.property⟩ : U) ∈ d.left}
  let rightT : Set T :=
    {t | (⟨t.val, hTU t.property⟩ : U) ∈ d.right}
  have hLeftClosed : (A.induce T hT).IsClosed leftT := by
    intro n F xs hxs y hy
    let ys : Fin n → U :=
      fun i => ⟨(xs i).val, hTU (xs i).property⟩
    have hys : ∀ i, ys i ∈ d.left := hxs
    have hyU :
        (⟨y.val, hTU y.property⟩ : U) ∈
          (A.induce U hU).func F ys := by
      change y.val ∈ A.func F (Subtype.val ∘ ys)
      exact hy
    exact d.left_closed F ys hys hyU
  have hRightClosed : (A.induce T hT).IsClosed rightT := by
    intro n F xs hxs y hy
    let ys : Fin n → U :=
      fun i => ⟨(xs i).val, hTU (xs i).property⟩
    have hys : ∀ i, ys i ∈ d.right := hxs
    have hyU :
        (⟨y.val, hTU y.property⟩ : U) ∈
          (A.induce U hU).func F ys := by
      change y.val ∈ A.func F (Subtype.val ∘ ys)
      exact hy
    exact d.right_closed F ys hys hyU
  have hCover : leftT ∪ rightT = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx :
        (⟨x.val, hTU x.property⟩ : U) ∈ d.left ∪ d.right := by
      rw [d.cover]
      exact Set.mem_univ _
    simpa only [leftT, rightT, Set.mem_union, Set.mem_setOf_eq] using hx
  have hLeftProper : leftT ≠ Set.univ := by
    obtain ⟨x, hxT, hxNot⟩ := Set.not_subset.mp hNotLeft
    intro hAll
    have hx : (⟨x, hxT⟩ : T) ∈ leftT := by
      rw [hAll]
      exact Set.mem_univ _
    exact hxNot ⟨⟨x, hTU hxT⟩, hx, rfl⟩
  have hRightProper : rightT ≠ Set.univ := by
    obtain ⟨x, hxT, hxNot⟩ := Set.not_subset.mp hNotRight
    intro hAll
    have hx : (⟨x, hxT⟩ : T) ∈ rightT := by
      rw [hAll]
      exact Set.mem_univ _
    exact hxNot ⟨⟨x, hTU hxT⟩, hx, rfl⟩
  let dT : (A.induce T hT).FreeDecomposition :=
    { left := leftT
      right := rightT
      left_closed := hLeftClosed
      right_closed := hRightClosed
      cover := hCover
      left_proper := hLeftProper
      right_proper := hRightProper
      rel_local := by
        intro n R xs hrel
        let ys : Fin n → U :=
          fun i => ⟨(xs i).val, hTU (xs i).property⟩
        have hyRel : (A.induce U hU).rel R ys := hrel
        rcases d.rel_local R ys hyRel with hl | hr
        · exact Or.inl (fun i => hl i)
        · exact Or.inr (fun i => hr i)
      func_cross_empty := by
        intro n F xs hx
        let ys : Fin n → U :=
          fun i => ⟨(xs i).val, hTU (xs i).property⟩
        have hCross :
            ¬ ((∀ i, ys i ∈ d.left) ∨
               (∀ i, ys i ∈ d.right)) := by
          intro h
          apply hx
          rcases h with hl | hr
          · exact Or.inl (fun i => hl i)
          · exact Or.inr (fun i => hr i)
        have hZero := d.func_cross_empty F ys hCross
        ext z
        constructor
        · intro hz
          have hzU :
              (⟨z.val, hTU z.property⟩ : U) ∈
                (A.induce U hU).func F ys := hz
          rw [hZero] at hzU
          exact (Set.not_mem_empty _ hzU).elim
        · intro hz
          exact (Set.not_mem_empty _ hz).elim }
  letI : IsEmpty ((A.induce T hT).FreeDecomposition) := hIrr
  exact isEmptyElim dT

end AllThoseEPPA.Applications.KOrientations
