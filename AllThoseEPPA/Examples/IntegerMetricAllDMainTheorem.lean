import AllThoseEPPA.Examples.IntegerMetricEPPAFromAmalgamation
import AllThoseEPPA.Examples.IntegerMetricAsReal
import AllThoseEPPA.Examples.IntegerMetricPullback
import AllThoseEPPA.Examples.IntegerMetricGluing
import AllThoseEPPA.Examples.IntegerMetricDisjointAmalgam
import AllThoseEPPA.Examples.IntegerMetricD1EPPA
import Lean.Elab.Tactic.Omega

/-!
# Strongened bounded-integer metric EPPA for every D, as a paper regression

The finite metric amalgamation law from the preceding module is
discharged via Mathlib's genuine real Metric.GlueSpace when the common
source is nonempty, and via the metric disjoint union otherwise.
Every input finite natural metric is represented as a real metric;
both source embeddings are real-isometric because their common
pulled-back natural distances coincide.

For D>=2 the manuscript's formalized faithful restricted/tree-like
EPPA theorem, the metric class amalgamation interface, local
finite metric completion and faithful unit-clique transfer finish
the genuine finite EPPA witness. D=0 and D=1 are already separately
proved and integrated in the project's established regressions.

The output theorem has only the mathematician-readable metric EPPA
quantifiers; no artificial structure parameters, Γ actions, or
hidden assumptions about small completions.
-/

namespace AllThoseEPPA
namespace IntegerMetric
namespace Bridge

universe u

/-- Every pair of finite metrics with distances in 0,...,D,
where D>0, can be amalgamated along arbitrary injective
maps from a common point type that induce identical old
distances. Neither common interface nor either side needs
to be nonempty. This is the EXACT amalgamation hypothesis
used by the paper's finite-class API. -/
theorem positiveDiameter_hasFiniteMetricAmalgamation
    (D : ℕ) (hD : 0 < D) :
    HasFiniteMetricAmalgamation.{u} D := by
  intro I X Y hFiniteX hFiniteY MX MY f g hAgree
  classical
  let MI : BoundedNatMetric D I :=
    MX.pullback f.toFun f.injective
  letI : MetricSpace I := MI.toNatMetric.toRealMetricSpace
  letI : MetricSpace X := MX.toNatMetric.toRealMetricSpace
  letI : MetricSpace Y := MY.toNatMetric.toRealMetricSpace
  have hX : ∀ x y : X,
      dist x y = (MX.dist x y : ℝ) := by
    intro x y
    rfl
  have hY : ∀ x y : Y,
      dist x y = (MY.dist x y : ℝ) := by
    intro x y
    rfl
  have hΦ : Isometry f.toFun := by
    apply Isometry.of_dist_eq
    intro i j
    change (MX.dist (f i) (f j) : ℝ) = (MI.dist i j : ℝ)
    rfl
  have hΨ : Isometry g.toFun := by
    apply Isometry.of_dist_eq
    intro i j
    change (MY.dist (g i) (g j) : ℝ) = (MI.dist i j : ℝ)
    exact congrArg (fun d : ℕ => (d : ℝ)) (hAgree i j).symm
  by_cases hNonempty : Nonempty I
  · letI : Nonempty I := hNonempty
    exact finiteAmalgam_viaRealGlue D hD MX MY hΦ hΨ hX hY
  · obtain ⟨W, hW, MW, jX, jY, hJX, hJY, _⟩ :=
      finiteDisjointAmalgam_viaRealSum D hD MX MY hX hY
    refine ⟨W, hW, MW, jX, jY, hJX, hJY, ?_⟩
    intro i
    exact (hNonempty ⟨i⟩).elim

/-- FULL strengthened user-requested regression: every finite
D-bounded integer metric has a finite D-bounded metric EPPA
witness preserving the maximum size of a unit-distance clique,
uniformly in ALL natural D, including 0, 1 and empty carriers.

For D>=2, this theorem derives from the verified general
EPPA construction in the paper; it does not use a separate
external metric EPPA theorem. -/
theorem allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique :
    AllFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique.{u} := by
  intro D
  by_cases hZero : D = 0
  · subst D
    exact finiteBoundedMetricsHaveEPPAAndPreserveUnitClique_zero
  by_cases hOne : D = 1
  · subst D
    exact finiteBoundedMetricsHaveEPPAAndPreserveUnitClique_one
  have hD : 1 < D := by omega
  exact unitCliquePreservingMetricEPPA_of_finiteMetricAmalgamation
    D hD (positiveDiameter_hasFiniteMetricAmalgamation D (by omega))

/-- The stronger metric theorem implies its ordinary EPPA
specialization with the same distance alphabet, as expected. -/
theorem allFiniteBoundedMetricsHaveEPPA :
    AllFiniteBoundedMetricsHaveEPPA.{u} := by
  intro D
  exact unitCliquePreservingEPPA_implies_EPPA
    D (allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique D)

end Bridge
end IntegerMetric
end AllThoseEPPA
