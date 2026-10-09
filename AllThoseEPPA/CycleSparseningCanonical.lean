import AllThoseEPPA.CycleSparseningIrreducible

/-!
# Canonical embedded copy for cycle sparsening

This file starts the formalization of Claim `c:cycles:emb`.  The first
ingredient is the paper's observation that, because the distinguished
relation is complete on the embedded copy of `A`, any two distinct embedded
vertices lying on the same bad induced cycle must be adjacent on that cycle.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w z

variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {α : Type w}
variable {β : Type z}
variable (act : L.Action Γ)
variable (A : Structure L α)
variable (B₀ : Structure L β)
variable (ψ : Structure.Embedding act A B₀)
variable (E : L.RelSymbol 2)

/-- Two distinct vertices from the embedded complete `E`-copy of `A`
which occur on a common bad cycle are consecutive on that cycle; according
to the displayed linear order this is either a non-wrap or the wrap edge. -/
theorem embedded_common_cycle_pair_classified
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (c : Structure.BadCycleSequence B₀ E)
    {a b : α}
    (hab : a ≠ b)
    (ha : ψ a ∈ c.carrier)
    (hb : ψ b ∈ c.carrier) :
    c.NonWrapPair (ψ a) (ψ b) ∨
      c.WrapPair (ψ a) (ψ b) := by
  have hAedge : A.Edge E a b :=
    (hcomplete a b).2 hab
  have hBedge : B₀.Edge E (ψ a) (ψ b) :=
    (Structure.Embedding.edge_map_iff
      ψ E hfix a b).2 hAedge
  rcases ha with ⟨i, hi⟩
  rcases hb with ⟨j, hj⟩
  have hedge :
      B₀.Edge E (c.vertex i) (c.vertex j) := by
    rw [hi, hj]
    exact hBedge
  have hcyc : Structure.CyclicAdjacent i j :=
    (c.edge_iff i j).1 hedge
  by_cases hlin : Structure.LinearAdjacent i j
  · exact Or.inl ⟨i, j, hi, hj, hcyc, hlin⟩
  · exact Or.inr ⟨i, j, hi, hj, hcyc, hlin⟩

end Sparsening
end AllThoseEPPA
