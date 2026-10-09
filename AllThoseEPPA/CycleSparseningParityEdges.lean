import AllThoseEPPA.CycleSparseningParityLift

/-!
# No unbroken lift of a bad induced E-cycle

The witness relation requires genericity of every edge tuple. Therefore
the Boolean cycle parity obstruction applies whenever all consecutive
edges of an indexed base bad cycle are lifted to E-edges in the sparsening
witness. This is the local obstruction used in `lem:sparsen`.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}
variable (B₀ : Structure L V) (E : L.RelSymbol 2)

/-- Every distinguished witness edge has generic centre valuation points. -/
theorem centerGeneric_of_edge
    (u v : WitnessVertex B₀ E)
    (hedge : (witnessStructure B₀ E).Edge E u v) :
    AreGeneric B₀ E (centerValuationPoint B₀ E u)
      (centerValuationPoint B₀ E v) := by
  change
    B₀.rel E
      (fun i => (Structure.pairTuple u v i).base B₀ E) ∧
    WitnessFamilyGeneric B₀ E (Structure.pairTuple u v) at hedge
  have hh := hedge.2 (0 : Fin 2) (1 : Fin 2)
    (centerPoint B₀ E u) (centerPoint B₀ E v)
  simpa only [Structure.pairTuple_zero, Structure.pairTuple_one,
    centerValuationPoint] using hh

/-- An induced bad E-cycle of the base witness cannot lift to a cycle of
the sparsening witness while preserving all its consecutive edges. -/
theorem no_edge_cycle_above_bad_cycle
    (c : Structure.BadCycleSequence B₀ E)
    (ws : Fin c.length → WitnessVertex B₀ E)
    (hbase : ∀ i, (ws i).base B₀ E = c.vertex i)
    (hstep :
      ∀ (i : Fin c.length) (hi : i.val + 1 < c.length),
        (witnessStructure B₀ E).Edge E
          (ws i) (ws ⟨i.val + 1, hi⟩))
    (hwrap :
      (witnessStructure B₀ E).Edge E
        (ws c.firstIndex) (ws c.lastIndex)) :
    False :=
  no_generic_edges_over_bad_cycle B₀ E c ws hbase
    (fun i hi =>
      centerGeneric_of_edge B₀ E (ws i) (ws ⟨i.val + 1, hi⟩)
        (hstep i hi))
    (centerGeneric_of_edge B₀ E
      (ws c.firstIndex) (ws c.lastIndex) hwrap)

end Sparsening
end AllThoseEPPA
