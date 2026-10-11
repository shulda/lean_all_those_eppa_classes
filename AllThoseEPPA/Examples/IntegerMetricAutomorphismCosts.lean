import AllThoseEPPA.Examples.IntegerMetricPartialCosts
import AllThoseEPPA.Examples.IntegerMetricEquivariance
import AllThoseEPPA.Automorphism
import Mathlib.Tactic.FinCases

/-!
# Every relational automorphism preserves the canonical metric completion

The checked shortest-path construction is functorial for
cost-preserving permutations. To turn this into an
automorphism-preserving completion of the partially
distance-coloured relational witness, we must show
the actual source-language automorphisms preserve the
canonical direct costs.

For a consistent partial distance-colour structure,
an old coloured edge receives its unique positive length
and a missing edge the default cost D. Every source
automorphism preserves and reflects all relation symbols
and therefore also preserves those direct costs. The
already checked walk-transport / shortest-path
equivariance theorem then turns its vertex permutation
into an isometry of the completed D-metric.

The statement works for arbitrary D>0 and needs no global
injectivity of homomorphism-embeddings and no finite
carrier. It is the exact automorphism-preservation lemma
needed to transfer EPPA from a restricted faithful
relational witness to its canonical metric completion.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Total Γ-automorphisms preserve and reflect every
individual distance-colour relation on a pair. The
symbol action is trivial. -/
theorem automorphism_edge_iff
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (g : Structure.Automorphism (action D) B)
    (d : Fin D) (x y : V) :
    B.rel (RelSymbol.edge d) ![g x, g y] ↔
      B.rel (RelSymbol.edge d) ![x, y] := by
  have h :=
    Structure.Automorphism.map_rel_iff
      g (RelSymbol.edge d) ![x,y]
  have ht :
      (g ∘ ![x,y]) = (![g x,g y] : Fin 2 → V) := by
    funext i
    fin_cases i <;> rfl
  simpa only [action_on_edge, ht] using h

/-- Every automorphism of a consistent partial
D-metric colour structure preserves its canonical
symmetrized direct costs exactly. -/
theorem candidateCost_automorphism_equivariant
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (g : Structure.Automorphism (action D) B)
    (x y : V) :
    candidateCost B (g x) (g y) = candidateCost B x y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [candidateCost]
  · have hGxy : g x ≠ g y := by
      intro he
      exact hxy (g.toEquiv.injective he)
    by_cases hLabel :
        ∃ d : Fin D, B.rel (RelSymbol.edge d) ![x,y]
    · obtain ⟨d,hd⟩ := hLabel
      have hG : B.rel (RelSymbol.edge d) ![g x,g y] :=
        (automorphism_edge_iff B g d x y).2 hd
      rw [candidateCost_of_edge B hB d hG,
        candidateCost_of_edge B hB d hd]
    · have hNoG :
          ¬ ∃ d : Fin D, B.rel (RelSymbol.edge d) ![g x,g y] := by
        rintro ⟨d,hd⟩
        apply hLabel
        exact ⟨d, (automorphism_edge_iff B g d x y).1 hd⟩
      rw [candidateCost_of_no_edge B hGxy hNoG,
        candidateCost_of_no_edge B hxy hLabel]

/-- A relational automorphism induces an isometry of
the canonical bounded metric completion on exactly the
same carrier (no arbitrary choices of paths or colours). -/
theorem completedMetric_automorphism_isometry
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (hB : IsConsistentPartialMetric B)
    (hD : 0 < D)
    (g : Structure.Automorphism (action D) B)
    (x y : V) :
    (toSymmetricCost B hB hD).completedMetric.dist (g x) (g y) =
      (toSymmetricCost B hB hD).completedMetric.dist x y := by
  exact (toSymmetricCost B hB hD).completedMetric_equivariant
    g.toEquiv
    (fun a b => candidateCost_automorphism_equivariant
      B hB g a b)
    x y

end Bridge
end IntegerMetric
end AllThoseEPPA
