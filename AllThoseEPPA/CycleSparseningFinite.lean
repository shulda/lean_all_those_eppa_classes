import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import AllThoseEPPA.CycleSparseningProjection

/-!
# Finiteness of the cycle-sparsening data

For a finite base witness, a bad cycle sequence has length at most the size of
the base carrier.  We encode it by this bounded length and its ordered vertex
map.  This gives finiteness of bad cycles, valuations, valuation structures,
and finally the whole cycle-sparsening witness.
-/

namespace AllThoseEPPA

universe u v

namespace Structure
namespace BadCycleSequence

variable {L : Language.{u}} {V : Type v}
variable {A : Structure L V} {E : L.RelSymbol 2}

/-- Bad induced cycle sequences over a finite carrier form a finite type. -/
theorem finite_of_finite [Finite V] :
    Finite (BadCycleSequence A E) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let Code :=
    Σ k : Fin (Fintype.card V + 1), Fin k.1 → V
  let code : BadCycleSequence A E → Code :=
    fun c =>
      ⟨⟨c.length,
          Nat.lt_succ_of_le
            (by
              simpa only [Fintype.card_fin] using
                (Fintype.card_le_of_injective
                  c.vertex c.injective))⟩,
        c.vertex⟩
  have hcode : Function.Injective code := by
    intro c d h
    apply ext_vertex c d
    · exact congrArg (fun z : Code => z.1.1) h
    · exact (Sigma.mk.inj_iff.mp h).2
  exact Finite.of_injective code hcode

end BadCycleSequence
end Structure

namespace Sparsening

variable {L : Language.{u}}
variable {V : Type v}
variable (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Cycle valuation functions are finite over a finite base carrier. -/
theorem valuationFunction_finite [Finite V] (x : V) :
    Finite (ValuationFunction B₀ E x) := by
  classical
  letI : Finite (Structure.BadCycleSequence B₀ E) :=
    Structure.BadCycleSequence.finite_of_finite
  letI : Fintype (Structure.BadCycleSequence B₀ E) :=
    Fintype.ofFinite _
  letI : Fintype (BadCyclesAt B₀ E x) :=
    Fintype.ofFinite _
  letI : Fintype (ValuationFunction B₀ E x) :=
    inferInstance
  exact Finite.of_fintype _

/-- Cycle valuation assignments over a one-point closure are finite. -/
theorem valuationAssignment_finite [Finite V] (x : V) :
    Finite (ValuationAssignment B₀ E x) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (B₀.closureAtSet x) :=
    Fintype.ofFinite _
  letI (y : B₀.closureAtSet x) :
      Finite (ValuationFunction B₀ E y.1) :=
    valuationFunction_finite B₀ E y.1
  letI (y : B₀.closureAtSet x) :
      Fintype (ValuationFunction B₀ E y.1) :=
    Fintype.ofFinite _
  letI : Fintype (ValuationAssignment B₀ E x) :=
    inferInstance
  exact Finite.of_fintype _

/-- Cycle valuation structures are finite over a finite base carrier. -/
theorem valuationStructure_finite [Finite V] (x : V) :
    Finite (ValuationStructure B₀ E x) := by
  letI : Finite (ValuationAssignment B₀ E x) :=
    valuationAssignment_finite B₀ E x
  infer_instance

/-- The cycle-sparsening witness has finite carrier over a finite base
witness. -/
theorem witnessVertex_finite [Finite V] :
    Finite (WitnessVertex B₀ E) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI (x : V) : Finite (ValuationStructure B₀ E x) :=
    valuationStructure_finite B₀ E x
  letI (x : V) : Fintype (ValuationStructure B₀ E x) :=
    Fintype.ofFinite _
  letI : Fintype (WitnessVertex B₀ E) :=
    inferInstance
  exact Finite.of_fintype _

end Sparsening
end AllThoseEPPA
