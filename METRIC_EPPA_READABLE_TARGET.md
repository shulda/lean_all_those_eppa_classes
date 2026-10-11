# Readable EPPA regression: bounded integer metric spaces

The theorem **proved in Lean** using the already-formalized general
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

## Exact Lean theorem and proof audit

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
It is a Prop-valued definition (not an axiom). The fully proved theorem
`IntegerMetric.Bridge.allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique`
in `AllThoseEPPA/Examples/IntegerMetricAllDMainTheorem.lean`
**inhabits that exact proposition for every D**, with no additional
hypotheses. The case D=0 has an identity-witness proof and the case
D=1 uses the checked finite-set EPPA construction. The full proof
passed Lean CI and the complete project axiom audit on PR #235;
its final import/integration is PR #237.

## What is being tested

The purpose is **not just to prove a true combinatorial theorem**.
The test checks whether the Lean versions of the paper's general
EPPA constructions are strong enough to *derive this completely
standalone statement*.

The completed proof **does** bridge the checked unrestricted faithful and
restricted/tree-like EPPA theorems to the above ordinary metric statement.
It uses ordinary finite metric amalgamation to complete the small
A-copy trees; local homomorphism-embedding metric completions give the
short-path certificate, while the faithful construction preserves the
maximum unit-clique number. No external metric EPPA theorem is assumed.
The separate locally finite subclass transfer theorem is already checked
but is not itself needed in this more direct faithful restricted-witness
application.

Current project state is recorded in [METRIC_EPPA_ROADMAP.md](METRIC_EPPA_ROADMAP.md).
The previously audited examples
`Hypergraph3.eppa` and `Hypergraph3.eppaK4Free` likewise have
self-contained quantified public statements.


## Why the extra clique condition is natural

For D >= 2, the completed proof combines two independently Lean-checked
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
partial bijections. The proof handles D=1 separately using the
already-formalized finite-set EPPA theorem. D=0 uses an explicit
identity-witness argument.
The strengthened statement includes all D, including 0 and 1.
The D=1 case is now formalized as
`finiteBoundedMetricsHaveEPPAAndPreserveUnitClique_one`
in `Examples/IntegerMetricD1EPPA.lean` (merged PR #205).

**Final audit trail (2026-10-11).** The faithful maximum-clique transfer
was checked and merged in PR #209. Exact metric shortest-path strong
completion, partial-isometry/automorphism bridges and real-metric rounding
were integrated in PRs #216–#230. Metric amalgamation is assembled from
Mathlib's real `Metric.GlueSpace` for nonempty interfaces (PR #221) and
real metric disjoint unions for empty interfaces (PR #222), with exact
integer-distance preservation after ceiling-and-cap truncation.
The manuscript-based conditional reduction is checked in PR #234.
The unconditional fully quantified strengthened metric EPPA theorem passed
the full Lean build and axiom audit in PR #235. Integration is tracked
in PRs #236–#237. See `METRIC_EPPA_ROADMAP.md` for dependencies and
merging information.
