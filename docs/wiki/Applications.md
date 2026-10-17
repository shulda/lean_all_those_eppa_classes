# Applications and mathematical regression tests

The mathematical distinction here is between (a) proving the
paper's **general constructions** and (b) fully identifying an
individual published application. A useful regression may be
strictly weaker than the paper's application without diminishing
the general theorem it tests.

## Finite 3-uniform hypergraphs

The code proves ordinary EPPA for finite 3-uniform hypergraphs
and separately for finite K₄^(3)-free 3-uniform hypergraphs.
The second is a real test of
**irreducible-structure faithfulness**: the finite witness stays
free of the forbidden four-vertex complete 3-hypergraph.

- [`Hypergraph3.eppa`](../../AllThoseEPPA/Examples/Hypergraph3.lean).
- [`Hypergraph3.eppaK4Free`](../../AllThoseEPPA/Examples/Hypergraph3K4Free.lean).

Both are derived from the general verified machinery and are
retained as independent regression theorems. Neither application
alone should be treated as a substitute for Theorem 1.1.

## Bounded integer metrics and unit-distance clique size

The theorem
[`IntegerMetric.Bridge.allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique`](../../AllThoseEPPA/Examples/IntegerMetricAllDMainTheorem.lean)
quantifies over **every** nonnegative integer D and **every**
finite metric input with distances in {0,...,D}. It produces
a finite witness with distances in the *same bound*, extends
all partial subset isometries, and has exactly the same
maximum size of a pairwise distance-one clique.

This is an exact, readable, useful theorem; the universal D
quantifier includes zero and one. It is **ordinary EPPA** in
the present exported form. The printed metric
Proposition 12.2 concerns **coherent EPPA** for the class
excluding a prescribed unit-distance clique and does not
present itself as a fixed-D metric theorem.

Consequently the Lean metric result has one additional
advantage (a global bound and an exact clique-number
preservation statement) but does **not**, just by its current
public type, formalize the printed *coherent* metric proposition.
For the full construction and usage, see
[`INTEGER_METRIC_EPPA_API.md`](../../INTEGER_METRIC_EPPA_API.md)
and [`METRIC_EPPA_ROADMAP.md`](../../METRIC_EPPA_ROADMAP.md).

## The genuine d-language of k-orientations

The public import is:

```lean
import AllThoseEPPA.KOrientationsEPPA

#check AllThoseEPPA.KOrientationsEPPA.rootedFaithfulCoherent
```

The theorem assumes an input finite digraph A with
`A.HasOutdegreeAtMost k` and **additionally**
`A.HasReachableRoots k`. It constructs an actual finite
k-orientation K with the same outdegree bound and reachable
roots, and a genuine embedding of the **full** original
`dStructure A k` into `dStructure K.graph k`.
Every original partial d-automorphism extends coherently,
and the witness is irreducible-structure faithful.

Importantly, the d-language here contains set-valued symbols
for **all positive arities**, not just a unary successor
surrogate. The two-stage verified construction transports
the actual original all-arity partial maps.

**But this is not all of printed Theorem 12.9.**
The [public paper](https://arxiv.org/abs/1902.03855)
states the theorem for the whole class of finite
k-orientations. Requiring every vertex to reach a root
is a real additional hypothesis: a finite directed cycle
with k=1 is a counterexample to the implication
“outdegree ≤ k implies reachable roots”.

See [`RootedKOrientationDFinalEPPA.lean`](../../AllThoseEPPA/Applications/KOrientations/RootedKOrientationDFinalEPPA.lean),
[`Graph.lean`](../../AllThoseEPPA/Applications/KOrientations/Graph.lean)
and the [k-orientation API guide](../../K_ORIENTATIONS_EPPA_API.md).
A bridge removing rootedness, or an updated printed theorem
with that hypothesis, is necessary before claiming exact
Theorem 12.9 correspondence.

## Further published applications

The paper also discusses finite structures with constants and
other representations of k-orientations. They may follow from
the main theorems, but this wiki does not report a separate
formalization of their printed end-statements without a
verified Lean declaration explicitly establishing the claim.

## Regression and future certification policy

For each new application, publish both its human-readable
mathematical quantifiers and the **exact Lean statement**.
Check the model encoding and whether extra hypotheses
restrict the source class. Derivability “in principle”
from a verified general theorem is different from a
kernel-checked source-facing endpoint.
