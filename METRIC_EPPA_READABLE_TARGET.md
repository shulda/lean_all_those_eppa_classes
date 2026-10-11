# Readable EPPA regression: bounded integer metric spaces

The theorem we want to derive from the already-formalized general
constructions has the following complete mathematical meaning.

> **For every natural number D**, every finite metric space A with
> distances in {0,1,...,D} is an isometric subspace of a finite metric
> space B with distances in the **same** set {0,1,...,D}, such that
> **every isometry between any two subsets of A extends to an
> isometry of B**.

There are **no auxiliary hypotheses** about an ordering, a particular
diameter, a chosen shortest-path operation, a Γ-action, a collection of
partial maps, or a representation by relational structures. D is
universally quantified, including D=0; the original point set A may
be empty. This is ordinary EPPA, not a statement about extending
the automorphisms of A itself only.

**Česky:** Pro každé přirozené D má každý konečný metrický prostor
se vzdálenostmi v {0,1,...,D} konečného EPPA svědka se vzdálenostmi
v téže množině. Každé částečné izometrii mezi libovolnými dvěma
podmnožinami původního prostoru odpovídá izometrie celého svědka,
která ji rozšiřuje.

## Exactly what Lean will check

The formal contract is `IntegerMetric.FiniteBoundedMetricsHaveEPPA D`
in [IntegerMetricReaderFacingEPPA.lean](AllThoseEPPA/Examples/IntegerMetricReaderFacingEPPA.lean).
Its statement spells out finite carriers, distances, the isometric
embedding, partial isometries of arbitrary subsets, and full
permutations of the witness. It does **not** refer to the private
`IsEPPAWitness` or `Homomorphism.IsHomomorphismEmbedding` predicates.

The final all-D target is
`IntegerMetric.AllFiniteBoundedMetricsHaveEPPA`,
which is currently **only a Prop-valued definition, NOT a proved
theorem and NOT an axiom**. The case D=0 is already a checked
theorem (`finiteBoundedMetricsHaveEPPA_zero`).

## What is being tested

The purpose is **not just to prove a true combinatorial theorem**.
The test checks whether the Lean versions of the paper's general
EPPA constructions are strong enough to *derive this completely
standalone statement*.

We may develop whichever intermediate representation and stronger
technical lemmas make the proof clearest. The **final proof** must
provide the bridge from the already-verified general EPPA theorem
(restricted/tree-like construction and locally finite completion
transfer) to the above straightforward metric statement. A separate
direct construction of metric EPPA alone would not test the scope of
the manuscript formalization; it would be an independent theorem
of a different kind.

Current project state is recorded in [METRIC_EPPA_ROADMAP.md](METRIC_EPPA_ROADMAP.md).
The previously audited examples
`Hypergraph3.eppa` and `Hypergraph3.eppaK4Free` likewise have
self-contained quantified public statements.
