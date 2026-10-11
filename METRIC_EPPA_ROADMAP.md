# Verified regression: EPPA for finite bounded integer metric spaces

## Authoritative mathematical statement

**Status: complete Lean proof, 2026-10-11.** The unconditional all-D
strengthened theorem passed the entire Lean build and axiom audit in
[PR #235](https://github.com/shulda/lean_all_those_eppa_classes/pull/235),
CI run `38161154070`. Integration into the authoritative `main` import graph was completed
through PRs #236 and #237; the docstring cleanup was merged in PR #239.

For **every** `D : ℕ`, each finite metric `A` with distances in
`{0,1,...,D}` admits a finite metric `B` with distances in the
**same** set, together with an isometric embedding `ι : A ↪ B`, such
that **every isometry between any two subsets of A** extends to a
global isometry of B, and

`maximumUnitCliqueSize B = maximumUnitCliqueSize A`.

This includes empty input spaces and `D=0,1`. There is no ordering,
auxiliary relation language, predetermined partial-map family, or
completion hypothesis in the reader-facing conclusion.

- **Exact proposition** (quantifiers expanded in the statement):
  `IntegerMetric.AllFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique`
  in `AllThoseEPPA/Examples/IntegerMetricReaderFacingEPPA.lean`.
- **Proof**:
  `IntegerMetric.Bridge.allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique`
  in `AllThoseEPPA/Examples/IntegerMetricAllDMainTheorem.lean`.
- **Ordinary EPPA corollary**:
  `IntegerMetric.Bridge.allFiniteBoundedMetricsHaveEPPA`,
  from the stronger theorem.

These are actual theorem declarations with proofs, not unproved
Prop-valued definitions declared as axioms.

## Checked proof architecture

For `D ≥ 2`, this application is **a regression test of the general
EPPA machinery of the manuscript**, not an independent invocation of
a previously known metric EPPA result:

1. **Encode complete integer metrics** in a purely relational language
   with one binary colour for each positive distance `1,...,D`
   and trivial symbol action. Actual isometries are precisely
   embeddings of the complete encodings; arbitrary partial
   isometries produce genuine partial automorphisms.
2. **Finite metric amalgamation:** Turn a natural-valued metric into a
   Mathlib real `MetricSpace`, transport the common interface
   isometrically, and glue using `Metric.GlueSpace` if it is
   nonempty; use `Metric.metricSpaceSum` if empty. The quotient
   of finite `X ⊕ Y` is finite. Applying
   `min D (Nat.ceil (dist x y))` gives another genuine bounded
   integer metric, preserves all original integral distances
   exactly, and (for the nonempty interface) identifies the
   prescribed pairs. This proves the explicit, otherwise
   conditional `Bridge.HasFiniteMetricAmalgamation D` law.
3. **Build an actual manuscript amalgamation class**
   `Bridge.finiteMetricEncodingAmalgamationClass`. Its members are
   exactly finite complete D-metric encodings. Importantly, a
   common source of two embeddings need not itself already be
   presented as a metric: exact relational embeddings induce
   matching pullback distances on it.
4. **Use the formalized paper constructions:** Start with
   `Faithful.finiteOrbitUnaryStructuresHaveFaithfulCoherentEPPA`;
   apply `TreeLike.restrictedEPPA_from_any_witness` with
   `n = max D 2`. The result is a finite **irreducible-structure
   faithful** relational EPPA witness whose small closed pieces
   homomorphism-embed into literal trees of complete copies of A.
5. **Complete the small pieces using the manuscript's real
   amalgamation API**, via
   `TreeLike.smallClosedTrees_haveCompletions` (Observation 9.4),
   and translate its *ordinary* K-homomorphism-embedding
   completions into `HasSmallMetricHomEmbCompletions` without
   assuming global injectivity.
6. **Shortest-path metric completion:** Positive integer edge
   weights give a canonical metric on the same finite carrier.
   Every hypothetical shortcut for an old edge has support at
   most `D`, so the local metric certificates rule it out.
   Source automorphisms act isometrically on the result.
7. **Clique-size preservation:** For `D≥2`, every distance-one
   edge in the completed metric was an original colour-one
   edge. Every complete colour-one clique is irreducible, so
   the faithful relational witness can move it into the copy
   of A. Isometric inclusion supplies the reverse inequality.
   This proves exact equality of maximum unit-clique sizes.
8. **Reader-facing translation:** The quantified result is
   stated only in terms of genuine bounded integer metrics,
   finite carriers, arbitrary subset isometries, permutations
   extending them, and numeric clique equality.

For `D=0`, the metric carrier has at most one point, and the
identity witness works. For `D=1`, finite metrics are discrete;
the already verified finite-set EPPA construction extends all
partial bijections on the *same* carrier. The shortest-path
'no new unit edges' observation is NOT valid at `D=1`,
which is why the branch is treated separately.

## Main Lean declarations and audit pointers

| Part | File / theorem | Audit |
| --- | --- | --- |
| Full ordinary metric contract | `Examples/IntegerMetricReaderFacingEPPA.lean` | PR #202 |
| Special cases `D=0,1` | `Examples/IntegerMetricReaderFacingEPPA.lean`, `IntegerMetricD1EPPA.lean` | PRs #202, #205 |
| Shortest-path metric, local preservation, automorphism lift | `Examples/IntegerMetricShortestPaths.lean`, `IntegerMetricLocalShortcuts.lean`, `IntegerMetricCanonicalAutomorphismLift.lean` | PRs #190–#216, #225 |
| Faithful maximum unit-clique equality | `Bridge.faithfulShortestPath_preserves_maximumUnitCliqueSize` | PR #209 |
| Exact canonical automorphism-preserving strong completion | `Examples/IntegerMetricAutPreservingStrongCompletion.lean` | PR #229 (integrated) |
| Metric↔relational exact embeddings and real rounding | `Examples/IntegerMetricEncodingIsometry.lean`, `IntegerMetricIsometriesToEmbeddings.lean`, `IntegerMetricRealRounding.lean` | PR #229 (integrated) |
| Ordinary K-small-completion ⇒ local metric certificates | `Bridge.smallClassCompletions_imply_smallMetricCompletions` | PR #232 |
| Metric pullback and agreement on general relational interface | `IntegerMetricPullback.lean`, `IntegerMetricParallelEmbeddings.lean` | PRs #231, #228 |
| Finite metric gluing, nonempty/empty common interface | `IntegerMetricGluing.lean`, `IntegerMetricDisjointAmalgam.lean` | PRs #221, #222 |
| Metric amalgamation ⇒ exact class API | `IntegerMetricAmalgamationClass.lean` | PR #234 dependency |
| General manuscript EPPA ⇒ stronger D-metric EPPA, conditional on metric AP | `Bridge.unitCliquePreservingMetricEPPA_of_finiteMetricAmalgamation` | PR #234, green run `38160937629` |
| Complete strengthened reader-facing theorem, all D | `Bridge.allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique` | PR #235, green run `38161154070` |

**Integration complete:** PR #236 consolidated the conditional
metric theorem on `main`; PR #237 added the real-metric gluing
and unconditional all-D theorem; both passed full CI and axiom audit
before merge. PR #239 fixed stale docstrings. For reuse from external
Lean projects, see [`INTEGER_METRIC_EPPA_API.md`](INTEGER_METRIC_EPPA_API.md)
and the one-import facade `AllThoseEPPA.IntegerMetricEPPA`.

GitHub Actions runs the entire Lean build and project axiom audit.
Project proofs do not rely on `sorryAx` or custom axioms; only the
accepted Lean/mathlib logical axioms (`propext`,
`Classical.choice`, `Quot.sound`) are permitted.

## What remains on the project roadmap

This strengthened integer-metric result is the **last planned small
regression**. The remaining separately scheduled large paper application
is the `k`-orientations with `d`-closures / Hrushovski-related case
(Section 9.3). A final manuscript-theorem-statement/API alignment audit
is also planned. Do not conflate these tasks with the metric regression.

For the complete earlier exploratory plan, failed proof attempts,
intermediate PR status and chronological audit notes, see
[the archived 2026-10-11 roadmap](METRIC_EPPA_ROADMAP_ARCHIVE_20261011.md).
