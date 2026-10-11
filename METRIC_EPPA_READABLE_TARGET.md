# Readable EPPA regression: bounded integer metric spaces

The theorem we want to derive from the already-formalized general
constructions has the following complete mathematical meaning.

> **For every natural number D**, every finite metric space A with
> distances in {0,1,...,D} is an isometric subspace of a finite metric
> space B with distances in the **same** set {0,1,...,D}, such that
> **every isometry between any two subsets of A extends to an
> isometry of B**. **Furthermore, the maximum cardinality of a
> set of pairwise distance-one points is equal in A and B.**

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
která ji rozšiřuje. **Navíc se zachová velikost největší množiny
bodů, v níž každé dva různé body mají vzdálenost 1.**

## Exactly what Lean will check

The **primary stronger contract** is
`IntegerMetric.FiniteBoundedMetricsHaveEPPAAndPreserveUnitClique D`
in [IntegerMetricReaderFacingEPPA.lean](AllThoseEPPA/Examples/IntegerMetricReaderFacingEPPA.lean).
Its statement spells out finite carriers, distances, the isometric
embedding, partial isometries of arbitrary subsets, full
permutations of the witness, and **equality of maximum distance-one
clique sizes**. The latter is defined by `IsUnitDistanceClique`
and `maximumUnitCliqueSize`. The numeric definition gives
0 for an empty metric space. The statement does **not** refer
to the private `IsEPPAWitness` or
`Homomorphism.IsHomomorphismEmbedding` predicates.

The weaker original contract `FiniteBoundedMetricsHaveEPPA D`
is retained for comparison, and is a verified logical consequence
of the stronger statement. The all-D strengthened target is
`AllFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique`.
It is currently **only a Prop-valued definition, NOT a proved
theorem and NOT an axiom**. The case D=0 has a checked explicit
identity-witness proof. The complete all-D claim remains open.

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


## Why the extra clique condition is natural

For D >= 2, the proof will exploit two independently checkable
mechanisms:

1. The faithful relational EPPA construction does not create a
   larger clique of positive distance-1 relation edges: every
   such finite clique is an irreducible induced structure,
   hence it can be moved by an automorphism into the embedded
   original A.
2. Canonical shortest-path completion does not turn a cost > 1
   into distance 1. Because every edge cost is a positive
   integer, a shortest walk of total cost 1 is one already
   labelled cost-1 edge. Unlabelled pairs have default cost D
   and hence cannot create new 1-edges when D >= 2.

**Special case D = 1.** Here *unlabelled* pairs are assigned
default cost 1, so the sentence “shortest-path completion never
introduces unit edges” is false as stated for this construction.
The resulting metric class is simply finite discrete spaces:
every distinct pair has distance 1, and partial isometries are
partial bijections. Handle D=1 separately using finite-set EPPA,
which is already formalized, or provide an equivalent exact
completion route. D=0 also has a separate trivial proof.
The strengthened statement includes all D, including 0 and 1.
The D=1 case is now formalized as
`finiteBoundedMetricsHaveEPPAAndPreserveUnitClique_one`
in `Examples/IntegerMetricD1EPPA.lean` (merged PR #205).

**What remains to prove:** the global all-D strengthened theorem.
The faithful clique irreducibility and cardinality transfer
(PRs #204/#206), the no-new-unit-edge shortest-path lemma
(PR #203), and maximum-clique-number arithmetic (PR #207)
are separately CI/axiom-audited. Their combined conditional
application is prepared in PR #209 and still needs its full
integration audit and the remaining metric EPPA construction.
Nothing is silently assumed by merely defining the target.
