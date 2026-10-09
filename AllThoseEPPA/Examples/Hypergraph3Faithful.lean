import AllThoseEPPA.Examples.Hypergraph3Bridge
import AllThoseEPPA.Automorphism
import Mathlib.Data.Set.Card

/-!
# Faithful ternary witnesses are genuine 3-uniform hypergraphs

Faithfulness says that the closure of every realised relational triple can
be moved inside the original hypergraph. This implies that every realised
triple has three distinct vertices and that its truth depends only on the
unordered three-element set, not on the ordering of the tuple.
-/

namespace Hypergraph3.Bridge

open AllThoseEPPA

universe u v

variable {α : Type u} {β : Type v}
variable (A : Hypergraph3 α) (B : AllThoseEPPA.Structure language β)
variable (ψ : AllThoseEPPA.Structure.Embedding action (toStructure A) B)
variable (hfaith : AllThoseEPPA.Structure.IsIrreducibleStructureFaithful action ψ)

/-- Every realised triple can be moved into the distinguished embedded copy,
where it is necessarily a hyperedge. -/
theorem relationTriple_movable
    (xs : Fin 3 → β) (hrel : B.rel RelSymbol.triple xs) :
    ∃ (g : AllThoseEPPA.Structure.Automorphism action B)
      (as : Fin 3 → α),
      (∀ i, g (xs i) = ψ (as i)) ∧ A.edge (Set.range as) := by
  let S : Set β := B.closureSet (Set.range xs)
  have hS : B.IsClosed S := B.isClosed_closureSet (Set.range xs)
  have hIr : (B.induce S hS).IsIrreducible := by
    change (B.closureStructure (Set.range xs)).IsIrreducible
    exact AllThoseEPPA.Structure.relationTupleClosure_isIrreducible
      B RelSymbol.triple xs hrel
  obtain ⟨g, hg⟩ := hfaith S hS hIr
  have hmem (i : Fin 3) : xs i ∈ S :=
    B.subset_closureSet (Set.range xs) ⟨i, rfl⟩
  have hpre : ∀ i : Fin 3, ∃ a : α, g (xs i) = ψ a := by
    intro i
    exact hg (xs i) (hmem i)
  choose as has using hpre
  refine ⟨g, as, has, ?_⟩
  have hgx : (g ∘ xs) = (ψ ∘ as) := by
    funext i
    exact has i
  have hglang : g.lang = 1 := Subsingleton.elim _ _
  have hψlang : ψ.lang = 1 := Subsingleton.elim _ _
  have hrelg : B.rel RelSymbol.triple (g ∘ xs) := by
    simpa only [hglang, Language.Action.onRel_one] using
      ((AllThoseEPPA.Structure.Automorphism.map_rel_iff
        g RelSymbol.triple xs).2 hrel)
  rw [hgx] at hrelg
  change (toStructure A).rel RelSymbol.triple as
  apply (ψ.map_rel_iff RelSymbol.triple as).1
  simpa only [hψlang, Language.Action.onRel_one] using hrelg

/-- Reordering a realised ternary tuple does not change the relation,
provided its set of vertices stays the same. -/
theorem relationTriple_reorder
    (xs ys : Fin 3 → β) (hrel : B.rel RelSymbol.triple xs)
    (hrange : Set.range xs = Set.range ys) :
    B.rel RelSymbol.triple ys := by
  obtain ⟨g, as, has, hA⟩ :=
    relationTriple_movable A B ψ hfaith xs hrel
  have hpre : ∀ i : Fin 3, ∃ a : α, g (ys i) = ψ a := by
    intro i
    have hi : ys i ∈ Set.range xs := by
      rw [hrange]
      exact ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hi
    exact ⟨as j, by rw [← hj]; exact has j⟩
  choose bs hbs using hpre
  have hgx : (g ∘ xs) = (ψ ∘ as) := by
    funext i
    exact has i
  have hgy : (g ∘ ys) = (ψ ∘ bs) := by
    funext i
    exact hbs i
  have hps : Set.range (ψ ∘ as) = Set.range (ψ ∘ bs) := by
    rw [← hgx, ← hgy, Set.range_comp, Set.range_comp, hrange]
  have himage : ψ '' Set.range as = ψ '' Set.range bs := by
    simpa only [Set.range_comp] using hps
  have hrangeA : Set.range as = Set.range bs :=
    (Set.image_injective.mpr ψ.injective) himage
  have hAys : A.edge (Set.range bs) := by
    rw [← hrangeA]
    exact hA
  have hψlang : ψ.lang = 1 := Subsingleton.elim _ _
  have hrelψ : B.rel RelSymbol.triple (ψ ∘ bs) := by
    have h := (ψ.map_rel_iff RelSymbol.triple bs).2
      (show (toStructure A).rel RelSymbol.triple bs from hAys)
    simpa only [hψlang, Language.Action.onRel_one] using h
  have hrelg : B.rel RelSymbol.triple (g ∘ ys) := by
    rw [hgy]
    exact hrelψ
  have hglang : g.lang = 1 := Subsingleton.elim _ _
  apply (AllThoseEPPA.Structure.Automorphism.map_rel_iff
    g RelSymbol.triple ys).1
  simpa only [hglang, Language.Action.onRel_one] using hrelg

/-- Faithfulness forbids degeneracies in realised ternary tuples. -/
theorem relationTriple_ncard
    (xs : Fin 3 → β) (hrel : B.rel RelSymbol.triple xs) :
    (Set.range xs).ncard = 3 := by
  obtain ⟨g, as, has, hA⟩ :=
    relationTriple_movable A B ψ hfaith xs hrel
  have hgx : g ∘ xs = ψ ∘ as := by
    funext i
    exact has i
  have hgcard :
      (Set.range (g ∘ xs)).ncard = (Set.range xs).ncard := by
    rw [Set.range_comp]
    exact Set.ncard_image_of_injective (Set.range xs) g.toEquiv.injective
  have hψcard :
      (Set.range (ψ ∘ as)).ncard = (Set.range as).ncard := by
    rw [Set.range_comp]
    exact Set.ncard_image_of_injective (Set.range as) ψ.injective
  rw [hgx] at hgcard
  exact hgcard.symm.trans (hψcard.trans (A.uniform _ hA))

/-- Interpret the faithful relational witness itself as a 3-uniform
hypergraph. Its edge set is the image of the realised ternary tuples. -/
def fromFaithfulStructure : Hypergraph3 β where
  edge e := ∃ xs : Fin 3 → β, B.rel RelSymbol.triple xs ∧ e = Set.range xs
  uniform := by
    rintro e ⟨xs, hrel, rfl⟩
    exact relationTriple_ncard A B ψ hfaith xs hrel

/-- No symmetrisation is needed: the original ternary relation already
coincides exactly with unordered hyperedge membership. -/
theorem fromFaithfulStructure_edge_iff
    (xs : Fin 3 → β) :
    (fromFaithfulStructure A B ψ hfaith).edge (Set.range xs) ↔
      B.rel RelSymbol.triple xs := by
  constructor
  · rintro ⟨ys, hrel, heq⟩
    exact relationTriple_reorder A B ψ hfaith ys xs hrel heq.symm
  · intro hrel
    exact ⟨xs, hrel, rfl⟩

end Hypergraph3.Bridge
