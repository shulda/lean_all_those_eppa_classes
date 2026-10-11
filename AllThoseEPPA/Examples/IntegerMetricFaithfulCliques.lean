import AllThoseEPPA.Examples.IntegerMetricBridge
import AllThoseEPPA.Irreducible
import Mathlib.Tactic.FinCases

/-!
# Every complete monochromatic binary clique is irreducible

Irreducible-structure faithfulness is strong enough to prevent
new large cliques in a binary relational EPPA witness. Indeed,
for any fixed positive-distance relation symbol, an induced
monochromatic clique is irreducible: if an alleged free
decomposition has points outside both sides, the binary edge
between those points necessarily crosses the decomposition.

This lemma is independent of the numerical metric properties
and works for any colour d : Fin D, any carrier and any
possibly empty or singleton vertex subset S. When applied
to the distance-one colour, the paper's irreducible-structure
faithfulness moves every unit-edge clique into the old copy
of A. A separate theorem will transport its full cardinality
and distance labels using the automorphism and the embedding.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Every vertex subset is closed in the pure relational
distance-colour language (there are no function symbols). -/
theorem allSubsetsClosed
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (S : Set V) :
    B.IsClosed S := by
  intro n F xs hxs
  exact F.elim

/-- If every distinct pair of a subset has one fixed binary
distance relation, its induced relational substructure is
irreducible. No completeness or metric triangle inequalities
are needed outside the chosen clique. -/
theorem monochromaticClique_isIrreducible
    {D : ℕ} {V : Type u}
    (B : Structure (language D) V)
    (d : Fin D)
    (S : Set V)
    (hClique :
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        B.rel (RelSymbol.edge d) ![x, y]) :
    (B.induce S (allSubsetsClosed B S)).IsIrreducible := by
  classical
  let hS : B.IsClosed S := allSubsetsClosed B S
  change (B.induce S hS).IsIrreducible
  constructor
  intro dec
  have hleft : ∃ x : S, x ∉ dec.left := by
    by_contra h
    apply dec.left_proper
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hright : ∃ y : S, y ∉ dec.right := by
    by_contra h
    apply dec.right_proper
    apply Set.eq_univ_of_forall
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hleft
  obtain ⟨y, hy⟩ := hright
  have hxy : x ≠ y := by
    intro he
    subst y
    have hcover : x ∈ dec.left ∪ dec.right := by
      rw [dec.cover]
      exact Set.mem_univ _
    rcases hcover with hxl | hyr
    · exact hx hxl
    · exact hy hyr
  have hxyV : x.1 ≠ y.1 := by
    intro he
    exact hxy (Subtype.ext he)
  let xs : Fin 2 → S := ![x, y]
  have hrel : (B.induce S hS).rel (RelSymbol.edge d) xs := by
    change B.rel (RelSymbol.edge d) (Subtype.val ∘ xs)
    have htuple :
        (Subtype.val ∘ xs) = (![x.1, y.1] : Fin 2 → V) := by
      funext i
      fin_cases i <;> rfl
    rw [htuple]
    exact hClique x.1 x.2 y.1 y.2 hxyV
  rcases dec.rel_local (RelSymbol.edge d) xs hrel with hl | hr
  · exact hx (hl 0)
  · exact hy (hr 1)

/-- Faithfulness now visibly applies to every monochromatic
clique: there is a witness automorphism moving the entire
chosen clique into the distinguished embedded original A.
This statement handles arbitrary finite and infinite subsets;
the next cardinality lemma will specialize to finite cliques. -/
theorem faithful_monochromaticClique_movable
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
    ∃ g : Structure.Automorphism (action D) B,
      ∀ x, x ∈ S → ∃ a : V, g x = ψ a :=
  hFaith S (allSubsetsClosed B S)
    (monochromaticClique_isIrreducible B d S hClique)

end Bridge
end IntegerMetric
end AllThoseEPPA
