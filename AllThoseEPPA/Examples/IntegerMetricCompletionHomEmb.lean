import AllThoseEPPA.Examples.IntegerMetricLocalShortcuts
import AllThoseEPPA.Examples.IntegerMetricAutomorphismCosts
import AllThoseEPPA.Irreducible
import Mathlib.Tactic.FinCases

/-!
# Canonical metric completion is a genuine homomorphism-embedding

The local shortest-path argument already shows that small ordinary metric
completions preserve every old distance label. The remaining semantic
requirement in the manuscript is reflection on *irreducible* substructures:
a completion can introduce a new distance-colour edge on an uncoloured
pair, but it may NOT introduce an edge inside an old irreducible piece.

In the purely binary metric language, any irreducible piece has an old
edge on every pair of distinct vertices. Otherwise deleting the two
unconnected vertices in turn gives an explicit free decomposition.
This observation yields the actual homomorphism-embedding certificate,
without assuming that a general homomorphism-embedding is injective.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- In a purely binary distance-colour language, an irreducible
structure cannot have an uncoloured pair of distinct vertices.
No symmetry or consistency assumption is needed: an old edge in
either orientation suffices. -/
theorem irreducible_has_coloured_pair
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hIrr : B.IsIrreducible)
    (x y : V) (hxy : x ≠ y) :
    ∃ d : Fin D,
      B.rel (RelSymbol.edge d) ![x,y] ∨
        B.rel (RelSymbol.edge d) ![y,x] := by
  classical
  by_contra hNo
  have hNoXY (d : Fin D) :
      ¬ B.rel (RelSymbol.edge d) ![x,y] :=
    fun hd => hNo ⟨d, Or.inl hd⟩
  have hNoYX (d : Fin D) :
      ¬ B.rel (RelSymbol.edge d) ![y,x] :=
    fun hd => hNo ⟨d, Or.inr hd⟩
  let decomp : B.FreeDecomposition := {
    left := {v : V | v ≠ y}
    right := {v : V | v ≠ x}
    left_closed := by
      intro n F xs hxs z hz
      exact F.elim
    right_closed := by
      intro n F xs hxs z hz
      exact F.elim
    cover := by
      apply Set.eq_univ_of_forall
      intro z
      change z ≠ y ∨ z ≠ x
      by_cases hzy : z = y
      · right
        intro hzx
        exact hxy (hzx.symm.trans hzy)
      · exact Or.inl hzy
    left_proper := by
      intro h
      have hy : y ∈ ({v : V | v ≠ y} : Set V) := by
        rw [h]
        exact Set.mem_univ y
      exact hy rfl
    right_proper := by
      intro h
      have hx : x ∈ ({v : V | v ≠ x} : Set V) := by
        rw [h]
        exact Set.mem_univ x
      exact hx rfl
    rel_local := by
      intro n R xs hR
      cases R with
      | edge d =>
          by_cases hy0 : xs 0 = y
          · right
            intro i
            fin_cases i
            · intro hx0
              exact hxy (hx0.symm.trans hy0)
            · intro hx1
              have ht : xs = (![y,x] : Fin 2 → V) := by
                funext j
                fin_cases j
                · exact hy0
                · exact hx1
              rw [ht] at hR
              exact hNoYX d hR
          · by_cases hy1 : xs 1 = y
            · right
              intro i
              fin_cases i
              · intro hx0
                have ht : xs = (![x,y] : Fin 2 → V) := by
                  funext j
                  fin_cases j
                  · exact hx0
                  · exact hy1
                rw [ht] at hR
                exact hNoXY d hR
              · intro hx1
                exact hxy (hx1.symm.trans hy1)
            · left
              intro i
              fin_cases i
              · exact hy0
              · exact hy1
    func_cross_empty := by
      intro n F xs hcross
      exact F.elim }
  exact hIrr.false decomp

/-- Relational completeness of any irreducible induced subset:
each pair of distinct points has at least one old colour in
one of the two orientations. -/
theorem irreducible_induced_has_coloured_pair
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (S : Set V) (hS : B.IsClosed S)
    (hIrr : (B.induce S hS).IsIrreducible)
    (x y : V) (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≠ y) :
    ∃ d : Fin D,
      B.rel (RelSymbol.edge d) ![x,y] ∨
        B.rel (RelSymbol.edge d) ![y,x] := by
  let X : S := ⟨x,hx⟩
  let Y : S := ⟨y,hy⟩
  have hXY : X ≠ Y := by
    intro h
    exact hxy (congrArg Subtype.val h)
  obtain ⟨d, h | h⟩ :=
    irreducible_has_coloured_pair (B.induce S hS) hIrr X Y hXY
  · refine ⟨d, Or.inl ?_⟩
    change B.rel (RelSymbol.edge d) (Subtype.val ∘ ![X,Y]) at h
    have ht :
        (Subtype.val ∘ (![X,Y] : Fin 2 → S)) =
          (![x,y] : Fin 2 → V) := by
      funext i
      fin_cases i <;> rfl
    rwa [ht] at h
  · refine ⟨d, Or.inr ?_⟩
    change B.rel (RelSymbol.edge d) (Subtype.val ∘ ![Y,X]) at h
    have ht :
        (Subtype.val ∘ (![Y,X] : Fin 2 → S)) =
          (![y,x] : Fin 2 → V) := by
      funext i
      fin_cases i <;> rfl
    rwa [ht] at h

/-- Identity on the points, regarded as a relational homomorphism
into an exact-edge-preserving canonical metric completion. -/
noncomputable def canonicalCompletionHom
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D)
    (hOld : ∀ (d : Fin D) (x y : V),
      B.rel (RelSymbol.edge d) ![x,y] →
      (toSymmetricCost B hB hD).completedMetric.dist x y = d.val + 1) :
    Structure.Homomorphism (action D) B
      (toStructure (toSymmetricCost B hB hD).completedMetric) where
  lang := 1
  toFun := id
  map_rel := by
    intro n R xs hR
    cases R with
    | edge d =>
        change (toSymmetricCost B hB hD).completedMetric.dist
          (xs 0) (xs 1) = d.val + 1
        have ht : xs = (![xs 0, xs 1] : Fin 2 → V) := by
          funext i
          fin_cases i <;> rfl
        have hPair : B.rel (RelSymbol.edge d) ![xs 0, xs 1] := by
          simpa only [ht] using hR
        exact hOld d (xs 0) (xs 1) hPair
  map_func := by
    intro n F xs
    exact F.elim

/-- The canonical metric completion is exact on EVERY irreducible
closed substructure: all pairs there already bore distance colours,
so no new relations can arise in such a piece. -/
theorem canonicalCompletionHom_isHomomorphismEmbedding
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D)
    (hOld : ∀ (d : Fin D) (x y : V),
      B.rel (RelSymbol.edge d) ![x,y] →
      (toSymmetricCost B hB hD).completedMetric.dist x y = d.val + 1) :
    Structure.Homomorphism.IsHomomorphismEmbedding (action D)
      (canonicalCompletionHom B hB hD hOld) := by
  intro S hS hIrr
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hxy
  · intro n R xs hxs
    cases R with
    | edge d =>
        change
          (toSymmetricCost B hB hD).completedMetric.dist
              (xs 0) (xs 1) = d.val + 1 ↔
            B.rel (RelSymbol.edge d) xs
        have ht : xs = (![xs 0, xs 1] : Fin 2 → V) := by
          funext i
          fin_cases i <;> rfl
        constructor
        · intro hd
          have hxy : xs 0 ≠ xs 1 := by
            intro heq
            have hzero :
                (toSymmetricCost B hB hD).completedMetric.dist
                  (xs 0) (xs 1) = 0 := by
              rw [heq]
              exact (toSymmetricCost B hB hD).completedMetric.dist_self _
            omega
          obtain ⟨e, he | he⟩ :=
            irreducible_induced_has_coloured_pair
              B S hS hIrr (xs 0) (xs 1)
              (hxs 0) (hxs 1) hxy
          · have heDist := hOld e (xs 0) (xs 1) he
            have hed : e = d := Fin.ext (by omega)
            simpa only [ht, hed] using he
          · have heForward :
                B.rel (RelSymbol.edge e) ![xs 0,xs 1] :=
              hB.symmetric e (xs 1) (xs 0) he
            have heDist := hOld e (xs 0) (xs 1) heForward
            have hed : e = d := Fin.ext (by omega)
            simpa only [ht, hed] using heForward
        · intro he
          have heForward :
              B.rel (RelSymbol.edge d) ![xs 0,xs 1] := by
            simpa only [ht] using he
          exact hOld d (xs 0) (xs 1) heForward
  · intro n F xs hxs
    exact F.elim

/-- The actual finite-local-completion hypothesis from the manuscript
gives a strong (injective) metric homomorphism-embedding on the SAME
carrier, not just an abstract short-path distance matrix. -/
theorem canonicalCompletion_homEmb_of_smallMetricCompletions
    {D : ℕ} {V : Type u} [Finite V]
    (B : Structure (language D) V)
    (hD : 0 < D)
    (hSmall : HasSmallMetricHomEmbCompletions B (max D 2)) :
    ∃ (hB : IsConsistentPartialMetric B)
      (f : Structure.Homomorphism (action D) B
        (toStructure (toSymmetricCost B hB hD).completedMetric)),
      Structure.Homomorphism.IsHomomorphismEmbedding
        (action D) f ∧ Function.Injective f.toFun := by
  obtain ⟨hB, hOld⟩ :=
    canonicalCompletion_preserves_oldEdges_of_smallMetricCompletions
      B hD hSmall
  refine ⟨hB, canonicalCompletionHom B hB hD hOld, ?_, ?_⟩
  · exact canonicalCompletionHom_isHomomorphismEmbedding
      B hB hD hOld
  · intro x y h
    exact h

end Bridge
end IntegerMetric
end AllThoseEPPA
