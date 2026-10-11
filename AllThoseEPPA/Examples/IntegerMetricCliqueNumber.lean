import AllThoseEPPA.Examples.IntegerMetricReaderFacingEPPA
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Elementary bounds for the readable maximum distance-one clique

The stronger human-readable EPPA test literally requires equality
of the MAXIMUM number of pairwise distance-one vertices.

To avoid hiding mathematical strength behind this numerical
definition, these lemmas provide two transparent mechanisms:

* Any exhibited finite unit clique has at most the defined
  maximum clique size.
* To bound the maximum clique size of B by that of A, it
  suffices to transport every unit clique of B to some unit
  clique of A of at least the same size.
* Every isometric embedding A -> B already gives the
  converse inequality automatically.

Thus irreducible-structure faithfulness needs to establish
only the explicit finite-clique transfer, and shortest-path
completion needs to preserve the set of unit edges.
-/

namespace AllThoseEPPA
namespace IntegerMetric

universe u

/-- The cardinality of any concrete unit-distance clique is
bounded by the maximum unit-distance clique size. -/
theorem unitClique_card_le_maximum
    {D : ℕ} {V : Type u} [Finite V]
    (M : BoundedNatMetric D V)
    (S : Finset V)
    (hClique : IsUnitDistanceClique M S) :
    S.card ≤ maximumUnitCliqueSize M := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  change S.card ≤
    (Finset.univ.powerset).sup
      (fun T : Finset V =>
        if IsUnitDistanceClique M T then T.card else 0)
  have hmem : S ∈ (Finset.univ : Finset V).powerset := by
    simp
  have hbound :=
    Finset.le_sup
      (s := (Finset.univ : Finset V).powerset)
      (f := fun T : Finset V =>
        if IsUnitDistanceClique M T then T.card else 0)
      hmem
  simpa only [if_pos hClique] using hbound

/-- An explicit pointwise clique transfer from B to A
implies the corresponding inequality of their largest
unit-distance clique cardinalities. -/
theorem maximumUnitCliqueSize_le_of_cliqueTransfer
    {D : ℕ} {V W : Type u} [Finite V] [Finite W]
    (A : BoundedNatMetric D V)
    (B : BoundedNatMetric D W)
    (hTransfer :
      ∀ S : Finset W, IsUnitDistanceClique B S →
        ∃ T : Finset V,
          IsUnitDistanceClique A T ∧ S.card ≤ T.card) :
    maximumUnitCliqueSize B ≤ maximumUnitCliqueSize A := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  change
    ((Finset.univ : Finset W).powerset).sup
      (fun S : Finset W =>
        if IsUnitDistanceClique B S then S.card else 0) ≤
      maximumUnitCliqueSize A
  apply Finset.sup_le
  intro S hS
  by_cases hClique : IsUnitDistanceClique B S
  · obtain ⟨T, hT, hcard⟩ := hTransfer S hClique
    calc
      (if IsUnitDistanceClique B S then S.card else 0) =
          S.card := if_pos hClique
      _ ≤ T.card := hcard
      _ ≤ maximumUnitCliqueSize A :=
        unitClique_card_le_maximum A T hT
  · simp only [if_neg hClique, zero_le]

/-- Isometric copies preserve unit edges and cardinalities of
finite cliques. Therefore the larger space cannot have a
*smaller* maximum unit-distance clique. -/
theorem maximumUnitCliqueSize_le_of_isometricEmbedding
    {D : ℕ} {V W : Type u} [Finite V] [Finite W]
    (A : BoundedNatMetric D V)
    (B : BoundedNatMetric D W)
    (ι : V ↪ W)
    (hIso : ∀ x y : V, B.dist (ι x) (ι y) = A.dist x y) :
    maximumUnitCliqueSize A ≤ maximumUnitCliqueSize B := by
  apply maximumUnitCliqueSize_le_of_cliqueTransfer B A
  intro S hS
  let T : Finset W := S.map ι
  have hT : IsUnitDistanceClique B T := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    have hab : a ≠ b := by
      intro he
      exact hxy (congrArg ι he)
    rw [hIso a b]
    exact hS a ha b hb hab
  refine ⟨T, hT, ?_⟩
  simp [T]

end IntegerMetric
end AllThoseEPPA
