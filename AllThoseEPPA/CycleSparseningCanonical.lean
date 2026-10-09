import AllThoseEPPA.CycleSparseningCycleGraph

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


/-- An induced bad cycle cannot contain three distinct vertices of the
embedded complete distinguished relation.  In the graph-theoretic language,
the copy of A is a clique whereas an induced cycle of length >= 4 is
triangle-free. -/
theorem embedded_bad_cycle_no_three
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (c : Structure.BadCycleSequence B₀ E)
    {a b d : α}
    (hab : a ≠ b) (hbd : b ≠ d) (hda : d ≠ a)
    (ha : ψ a ∈ c.carrier)
    (hb : ψ b ∈ c.carrier)
    (hd : ψ d ∈ c.carrier) : False := by
  rcases ha with ⟨i, hi⟩
  rcases hb with ⟨j, hj⟩
  rcases hd with ⟨l, hl⟩
  have hij : B₀.Edge E (c.vertex i) (c.vertex j) := by
    rw [hi, hj]
    exact (Structure.Embedding.edge_map_iff ψ E hfix a b).2
      ((hcomplete a b).2 hab)
  have hjl : B₀.Edge E (c.vertex j) (c.vertex l) := by
    rw [hj, hl]
    exact (Structure.Embedding.edge_map_iff ψ E hfix b d).2
      ((hcomplete b d).2 hbd)
  have hli : B₀.Edge E (c.vertex l) (c.vertex i) := by
    rw [hl, hi]
    exact (Structure.Embedding.edge_map_iff ψ E hfix d a).2
      ((hcomplete d a).2 hda)
  exact c.no_edge_triangle i j l hij hjl hli

end Sparsening
end AllThoseEPPA
