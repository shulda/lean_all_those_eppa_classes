import AllThoseEPPA.CycleSparseningEdgeCount
import Mathlib.Data.Set.Card
import Lean.Elab.Tactic.Omega

/-!
# The full induced-cycle sparsening trichotomy

The final combinatorial conclusion of `lem:sparsen`, formulated in terms of
finite vertex sets and directed E-edge counts. No genericity hypothesis
is imposed on S.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v
variable {L : Language.{u}} [L.HasUnaryFunctions] {V : Type v}
variable (B₀ : Structure L V) (E : L.RelSymbol 2)

/-- S contains an induced E-cycle of length at least four. -/
def ContainsInducedCycle (S : Set (WitnessVertex B₀ E)) : Prop :=
  ∃ c : Structure.BadCycleSequence (witnessStructure B₀ E) E,
    c.carrier ⊆ S

/-- A noninjective projection of a finite witness subset strictly reduces
the number of vertices. -/
theorem projected_vertices_strict_of_not_injOn [Finite V]
    (S : Set (WitnessVertex B₀ E))
    (hnot : ¬ Set.InjOn (fun w => w.base B₀ E) S) :
    (Set.image (fun w => w.base B₀ E) S).ncard < S.ncard := by
  letI : Finite (WitnessVertex B₀ E) := witnessVertex_finite B₀ E
  have hs : S.Finite := Set.toFinite S
  have hle :
      (Set.image (fun w => w.base B₀ E) S).ncard ≤ S.ncard :=
    Set.ncard_image_le hs
  have hneq :
      (Set.image (fun w => w.base B₀ E) S).ncard ≠ S.ncard := by
    intro heq
    exact hnot (Set.injOn_of_ncard_image_eq heq hs)
  omega

/-- **The finite counting part of Lemma `lem:sparsen`.**
For every vertex set S in the new witness, either S contains no induced
E-cycle of length at least four, or the projection loses a vertex, or
the projected set has strictly more directed E-edges. -/
theorem sparsening_trichotomy [Finite V]
    (S : Set (WitnessVertex B₀ E)) :
    ¬ ContainsInducedCycle B₀ E S ∨
      (Set.image (fun w => w.base B₀ E) S).ncard < S.ncard ∨
      Nat.card (EdgePairs (witnessStructure B₀ E) E S) <
        Nat.card (EdgePairs B₀ E
          (Set.image (fun w => w.base B₀ E) S)) := by
  classical
  by_cases hcycle : ContainsInducedCycle B₀ E S
  · rcases hcycle with ⟨c, hc⟩
    by_cases hinj : Set.InjOn (fun w => w.base B₀ E) S
    · exact Or.inr (Or.inr
        (bad_cycle_projected_edges_strict B₀ E S c hc hinj))
    · exact Or.inr (Or.inl
        (projected_vertices_strict_of_not_injOn B₀ E S hinj))
  · exact Or.inl hcycle

end Sparsening
end AllThoseEPPA
