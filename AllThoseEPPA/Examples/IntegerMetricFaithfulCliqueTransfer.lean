import AllThoseEPPA.Examples.IntegerMetricFaithfulCliques
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-!
# Irreducible-structure faithfulness preserves clique cardinalities

Given a Γ-embedding ψ:A→B and an irreducible-structure faithful
EPPA witness B, any monochromatic binary clique of B
can be moved by a B-automorphism into ψ(A). The inverse of ψ
therefore assigns DISTINCT original A vertices to the
clique's vertices and reflects their full monochromatic
edge relation. The induced set of A vertices has the
SAME cardinality as the clique in B.

This proves the relational half of the strengthened metric
EPPA regression: faithfulness prevents the formation of any
larger unit-edge clique, not merely a forbidden fixed-size
clique. The other half is the separate shortest-path lemma:
for D>=2 the metric completion never creates new unit edges.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Faithfulness transports ANY monochromatic distance-colour
clique in the witness to an equally large monochromatic clique
inside A. The statement uses only the paper's actual embedding,
automorphism and irreducible-structure faithfulness APIs. -/
theorem faithful_monochromaticClique_preserves_cardinality
    {D : ℕ} {V W : Type u}
    (A : Structure (language D) V)
    (B : Structure (language D) W)
    (ψ : Structure.Embedding (action D) A B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (action D) ψ)
    (d : Fin D)
    (S : Set W)
    (hClique :
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        B.rel (RelSymbol.edge d) ![x, y]) :
    ∃ T : Set V,
      T.ncard = S.ncard ∧
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
        A.rel (RelSymbol.edge d) ![x, y] := by
  classical
  obtain ⟨g, hmove⟩ :=
    faithful_monochromaticClique_movable
      A B ψ hFaith d S hClique
  let pre (x : S) : V :=
    Classical.choose (hmove x.1 x.2)
  have hpre (x : S) : g x.1 = ψ (pre x) :=
    Classical.choose_spec (hmove x.1 x.2)
  have hpreinj : Function.Injective pre := by
    intro x y hxy
    apply Subtype.ext
    apply g.toEquiv.injective
    change g x.1 = g y.1
    rw [hpre x, hpre y, hxy]
  let T : Set V := Set.range pre
  refine ⟨T, ?_, ?_⟩
  · calc
      T.ncard = Nat.card S :=
        Set.ncard_range_of_injective hpreinj
      _ = S.ncard := Nat.card_coe_set_eq S
  · intro a ha b hb hab
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    have hxy : x.1 ≠ y.1 := by
      intro he
      apply hab
      exact congrArg pre (Subtype.ext he)
    let xs : Fin 2 → W := ![x.1, y.1]
    have hOld : B.rel (RelSymbol.edge d) xs :=
      hClique x.1 x.2 y.1 y.2 hxy
    have hMoved : B.rel (RelSymbol.edge d) (g ∘ xs) := by
      simpa only [action_on_edge] using
        ((Structure.Automorphism.map_rel_iff
          g (RelSymbol.edge d) xs).2 hOld)
    let ys : Fin 2 → V := ![pre x, pre y]
    have hTuple : (g ∘ xs) = (ψ.toFun ∘ ys) := by
      funext i
      fin_cases i
      · exact hpre x
      · exact hpre y
    rw [hTuple] at hMoved
    have hA : A.rel (RelSymbol.edge d) ys := by
      apply (ψ.map_rel_iff (RelSymbol.edge d) ys).1
      simpa only [action_on_edge] using hMoved
    exact hA

end Bridge
end IntegerMetric
end AllThoseEPPA
