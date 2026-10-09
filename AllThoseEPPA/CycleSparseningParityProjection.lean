import AllThoseEPPA.CycleSparseningParityEdges

/-!
# A projected induced E-cycle cannot be reflected by the sparsening projection

This is the graph-theoretic form of the Boolean parity obstruction:
an induced E-cycle in the sparsening witness cannot project injectively
to an induced E-cycle in the base witness.  It is the bridge to the
edge-count trichotomy of `lem:sparsen`.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}
variable (B₀ : Structure L V) (E : L.RelSymbol 2)

/-- No bad induced witness cycle has an E-graph embedding as its projection
to B₀, even under a hypothesis only reflecting E-edges on that cycle. -/
theorem no_induced_cycle_of_projection_E_embedding
    (c : Structure.BadCycleSequence (witnessStructure B₀ E) E)
    (hinj : Set.InjOn
      (fun w : WitnessVertex B₀ E => w.base B₀ E) c.carrier)
    (hreflect :
      ∀ ⦃x y : WitnessVertex B₀ E⦄,
        x ∈ c.carrier → y ∈ c.carrier →
        B₀.Edge E (x.base B₀ E) (y.base B₀ E) →
          (witnessStructure B₀ E).Edge E x y) :
    False := by
  let d : Structure.BadCycleSequence B₀ E :=
    { length := c.length
      length_ge_four := c.length_ge_four
      vertex := fun i => (c.vertex i).base B₀ E
      injective := by
        intro i j hij
        apply c.injective
        exact hinj ⟨i, rfl⟩ ⟨j, rfl⟩ hij
      edge_iff := by
        intro i j
        constructor
        · intro h
          have he : (witnessStructure B₀ E).Edge E
              (c.vertex i) (c.vertex j) :=
            hreflect ⟨i, rfl⟩ ⟨j, rfl⟩ h
          exact (c.edge_iff i j).1 he
        · intro h
          have he := (c.edge_iff i j).2 h
          exact he.1 }
  let ws : Fin d.length → WitnessVertex B₀ E := c.vertex
  have hbase : ∀ i, (ws i).base B₀ E = d.vertex i := by
    intro i
    rfl
  have hstep :
      ∀ (i : Fin d.length) (hi : i.val + 1 < d.length),
        (witnessStructure B₀ E).Edge E
          (ws i) (ws ⟨i.val + 1, hi⟩) := by
    intro i hi
    have hcyc : Structure.CyclicAdjacent i
        (⟨i.val + 1, hi⟩ : Fin d.length) := by
      left
      change i.val + 1 = (i.val + 1) % d.length
      exact (Nat.mod_eq_of_lt hi).symm
    exact (c.edge_iff i ⟨i.val + 1, hi⟩).2 hcyc
  have hwrap :
      (witnessStructure B₀ E).Edge E
        (ws d.firstIndex) (ws d.lastIndex) := by
    have hadj : Structure.CyclicAdjacent d.firstIndex d.lastIndex := by
      right
      change (d.firstIndex).val =
        ((d.lastIndex).val + 1) % d.length
      have hlen : (d.lastIndex).val + 1 = d.length := by
        dsimp [Structure.BadCycleSequence.lastIndex]
        have hk := d.length_ge_four
        omega
      rw [hlen, Nat.mod_self]
      rfl
    exact (c.edge_iff d.firstIndex d.lastIndex).2 hadj
  exact no_edge_cycle_above_bad_cycle B₀ E d ws hbase hstep hwrap

end Sparsening
end AllThoseEPPA
