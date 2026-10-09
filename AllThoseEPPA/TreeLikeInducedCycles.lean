import AllThoseEPPA.TreeLikeGraphInterface
import AllThoseEPPA.CycleSparseningTrichotomy

/-!
# Induced cycles and closed induced substructures

The trichotomy of `lem:sparsen` tells us that a chosen *subset*
of witness vertices has no induced E-cycle. The chordal graph
argument of `lem:cuts` is applied instead to the structure
induced on that subset. This file proves the necessary transport:
any bad induced cycle in a closed induced substructure lifts to
one in the ambient structure, with carrier inside the subset.

Thus the no-cycle branch of the sparsening trichotomy can be
used directly in the chordal-cut argument.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A bad E-cycle in an induced closed substructure is also a bad
E-cycle in the ambient structure. The inverse implication does not
require closedness either; we use `induce` because the EPPA API
represents genuine substructures only on closed subsets. -/
def liftBadCycle
    (B : Structure L V) (E : L.RelSymbol 2)
    (S : Set V) (hS : B.IsClosed S)
    (c : Structure.BadCycleSequence (B.induce S hS) E) :
    Structure.BadCycleSequence B E where
  length := c.length
  length_ge_four := c.length_ge_four
  vertex := fun i => (c.vertex i).1
  injective := Subtype.val_injective.comp c.injective
  edge_iff := by
    intro i j
    have hc := c.edge_iff i j
    change B.rel E
      (Subtype.val ∘ Structure.pairTuple (c.vertex i) (c.vertex j)) ↔
        Structure.CyclicAdjacent i j at hc
    rw [Structure.pairTuple_map] at hc
    exact hc

/-- The lifted bad cycle has all its vertices inside the
original vertex set of the induced substructure. -/
theorem liftBadCycle_carrier_subset
    (B : Structure L V) (E : L.RelSymbol 2)
    (S : Set V) (hS : B.IsClosed S)
    (c : Structure.BadCycleSequence (B.induce S hS) E) :
    (liftBadCycle B E S hS c).carrier ⊆ S := by
  intro x hx
  rcases hx with ⟨i, hi⟩
  rw [← hi]
  exact (c.vertex i).2

/-- No induced cycle in a subset implies no induced cycle in
the closed substructure on that subset. -/
theorem no_bad_cycle_induced
    (B : Structure L V) (E : L.RelSymbol 2)
    (S : Set V) (hS : B.IsClosed S)
    (hNo : ¬ ∃ c : Structure.BadCycleSequence B E, c.carrier ⊆ S) :
    ∀ c : Structure.BadCycleSequence (B.induce S hS) E, False := by
  intro c
  exact hNo ⟨liftBadCycle B E S hS c,
    liftBadCycle_carrier_subset B E S hS c⟩

end TreeLike

namespace TreeLike

universe w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {V : Type w}

/-- **Sparsening-to-chordal bridge.** The first alternative of
the existing sparsening trichotomy gives a substructure with no
bad induced E-cycles whenever the selected subset is closed. -/
theorem sparsening_no_bad_cycle_induced
    (B₀ : Structure L V) (E : L.RelSymbol 2)
    (S : Set (Sparsening.WitnessVertex B₀ E))
    (hS : (Sparsening.witnessStructure B₀ E).IsClosed S)
    (hNo : ¬ Sparsening.ContainsInducedCycle B₀ E S) :
    ∀ c : Structure.BadCycleSequence
      ((Sparsening.witnessStructure B₀ E).induce S hS) E, False :=
  no_bad_cycle_induced
    (Sparsening.witnessStructure B₀ E) E S hS hNo

end TreeLike
end AllThoseEPPA
