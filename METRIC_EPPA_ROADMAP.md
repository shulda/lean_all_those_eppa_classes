# Next regression: EPPA for finite integer metric spaces, uniformly in D

**Scope.** For every natural number D and every finite metric space A with
distances in {0,1,...,D}, construct a finite *metric* EPPA witness with the
same distance alphabet. Target both a human-readable ordinary-EPPA theorem
and, if the verified machinery makes it convenient, coherent EPPA.

**Authoritative checkpoint (2026-10-11).** The principal paper theorems
including Proposition 11.3 are already Lean-formalized on `main` (PR #189,
green complete build and axiom audit). The **uniform all-D metric EPPA
regression is NOT yet proved**; the degenerate D=0 case is already proved.
The following first stages are checked and merged:

- PR #188: `IntegerMetricBasic.lean` and `IntegerMetricBridge.lean`,
  bounded integer metric vocabulary, relational distance encoding and
  ordinary EPPA for D=0; green complete CI and axiom audit.
- PR #190: `IntegerMetricShortestPaths.lean`, minimal weighted walks
  construct a D-bounded metric on the same carrier; green complete CI,
  axiom audit of 3,157 declarations.
- PR #191: `IntegerMetricNoShortcuts.lean`, precise iff for preservation
  of any prescribed direct edge cost, steps ≤ walk weight, and idempotence
  on already-metric costs; green complete CI, axiom audit of 3,174 declarations.
- PR #192: `IntegerMetricWalkSupport.lean`, proven finite-vertex support
  bound for every shortcut (at most D vertices); green build and axiom audit.
- PR #193: `IntegerMetricEquivariance.lean`, every cost-preserving
  permutation becomes an isometry of the shortest-path completion;
  merged and fully CI/axiom-audited.
- PR #194: `IntegerMetricLocalCertificates.lean`, a family of metric
  certificates for all potential shortcuts on at most D vertices
  excludes every shortcut, WITHOUT injectivity of the vertex maps;
  merged after full CI and axiom audit.
- PR #196: `IntegerMetricPartialCosts.lean`, canonical symmetric direct
  costs for loop-free, symmetric, uniquely coloured partial structures;
  merged after full CI and axiom audit.
- PR #198: `IntegerMetricPairModels.lean`, exact metric models for
  each coloured pair imply precisely the three shape conditions;
  merged after full CI and axiom audit.

**CI-pending integration branches:** #195 turns complete encoded-metric
homomorphisms into isometries; #197 proves every shortcut consists of
already-labelled edges; #199 proves an old coloured pair is irreducible;
#200 extracts exact pair models from an arbitrary homomorphism-embedding
into a metric. No all-D EPPA claim is made by any of these.


## Chosen route

Use the already verified restricted/tree-like theorem `thm:maintree`
and the already verified locally finite completion transfer
`thm:mainstrong` (Theorem 1.6). The proof does *not* need
Proposition 11.3, which is now independently formalized but not needed for this application.

1. **Encoding.** For each fixed D, build an ordinary relational Γ-language
   (Γ trivial) with symmetric positive-arity binary distance symbols
   `R_d` for d = 1,...,D, and no function symbols. Interpret a D-bounded
   integer metric as a complete undirected graph with exactly one colour
   per unordered pair of distinct vertices. Give explicit embeddings,
   partial automorphisms and their translation to isometries. For D=0,
   the class consists only of carrier types of size at most one.

2. **Ambient coherent EPPA.** Take the ambient class E to be *all* finite
   structures in this relational language; ordinary/coherent EPPA follows
   from the verified general relational theorem. It is not necessary
   for the ambient witness itself to be a metric or even a partial metric:
   the conditional local completion hypothesis controls later witnesses.

3. **Canonical shortest-path completion.** For a finite, partially
   distance-labelled relational structure B, define the path length as
   the sum of positive edge lengths, and complete missing distances by
   the minimum of D and the length of a shortest labelled path. Use D
   when there is no path. Prove symmetry, strict positivity off the
   diagonal, boundedness, and the triangle inequality (capped addition
   is subadditive). The construction is intrinsically invariant under
   every automorphism of B, so automorphisms lift *coherently* without
   making arbitrary choices.

4. **Local finite obstruction bound.** Require ordinary K-completions of
   all closed substructures on at most `max D 2` vertices (or use the
   slightly safer `max (D+1) 2`). Such completions forbid loops,
   asymmetry and conflicting colours on a pair. They also forbid any
   prescribed d-edge whose endpoints are connected by a labelled path
   of total weight < d: each edge has positive weight, hence such a path
   has fewer than d edges and visits at most d distinct vertices
   (therefore at most D vertices). This sharper finite-support estimate
   is the target of PR #192.
   Even an ordinary homomorphism-embedding completion, not assumed
   globally injective, suffices: each existing labelled edge is mapped
   to an edge of precisely the same distance, and triangle inequalities
   along its image still prohibit the shortcut. Consequently canonical
   completion preserves all old relation data in the precise
   `IsHomomorphismEmbedding` sense (on irreducible subsets).

5. **Class API.** Package the metric class as a finite hereditary
   strong-amalgamation class. Amalgamate metrics over a common induced
   subspace by gluing the carriers and using the bounded shortest-path
   metric on the union of their coloured edges. Prove that the canonical
   embeddings remain exact isometries; any shortcut through the other
   side can be contracted via triangle inequalities in the shared
   interface. The pushout has exact overlap (strong amalgamation).
   Establish all hypotheses of `locallyFiniteSubclass_hasCoherentEPPA`
   and derive the class-level theorem.

6. **Reader-facing regression.** Finish with a standalone theorem whose
   conclusion says: for every finite D-bounded integer metric A, there
   exist a finite D-bounded integer metric B and an isometric embedding
   i:A→B such that every partial isometry of A extends to a total
   isometry of B. The statement must *not* merely be an internal EPPA
   predicate. Prove D=0 rather than silently assuming D>0.

## Things to audit explicitly

* New binary relation symbols have *positive* arity and there are no
  unary or nullary relation loopholes.
* Ordinary homomorphism-embeddings need not be globally injective, even
  on short paths; the shortcut obstruction argument must not assume it.
* The completion must preserve all *existing* edge distances, rather
  than merely produce some bounded metric on the same carrier.
* A canonical completion is automorphism-equivariant, including
  reflection of relational tuples on each irreducible closed subset.
* The D=0 case must not be discarded by the `D>0` hypothesis of the
  truncation lemma.
* No external metric-space EPPA theorem may be used as an unproved
  assumption. The objective is to test the already formalized main
  machinery on a new nontrivial concrete class.

## Next mathematical obligations (after the checked foundations)

1. **Induced-pair exactness.** Finish PRs #195, #197, #199 and #200,
   then derive exact pair models from ordinary
   homomorphism-embedding completions of the induced singleton
   and two-point structures. Since an old relation tuple
   generates an irreducible closure, reflection holds on that pair,
   even though the completion need not be globally injective.
   Apply the checked #198 lemma to prove the shape axioms.
2. **Actual local path realizations.** From a completion of the induced
   support of a potentially shortening path (at most D vertices),
   extract the finite metric certificate in the checked PR #194.
   PR #197 provides the other key fact: all edges of such a
   short walk were already labelled, so ordinary homomorphism
   preservation suffices. Prove no-shortcut preservation of
   every OLD labelled edge and automorphism preservation by #193.
3. **Metric SAP / trees.** Prove that tree amalgamations of complete
   copies of a D-metric A admit exact bounded metric completions.
   Prefer shortest-path free amalgamation. For the full class-level
   Theorem 1.6 interface also prove hereditary strong amalgamation
   of finite D-metrics with the exact-overlap condition. A direct
   `thm:maintree` route can use the weaker exact tree case.
4. **Class-level theorem and regression.** Instantiate the checked
   local-finiteness transfer and derive a standalone ordinary EPPA
   theorem for all D>0, preferably coherent EPPA using canonical
   equivariance; join the checked D=0 case. Spell out
   finite isometric embeddings and partial-isometry extension.

Keep `max D 2` as a safe local consistency bound. The existing
abstract small-certificate and path-support theorems are NOT yet
the complete local-finiteness proof; the concrete induced-substructure
bridges above are essential.

**Small-bound note.** For a direct edge d≤D shortened by a weighted
walk, its total walk cost is <d and every step costs ≥1. Hence the
number of steps is <d and the visited-vertex set has cardinality
at most d≤D. The separate `max D 2` includes pair-consistency
witnesses even when D=1. No optimisation of D beyond this is needed.


## Strengthened regression (2026-10-11): preserve the unit-clique number

**New primary readable assertion:** for every D, the finite EPPA witness B
can be chosen so that its largest set of pairwise distance-1 vertices
has exactly the same cardinality as in A. The standalone target is
`FiniteBoundedMetricsHaveEPPAAndPreserveUnitClique D`;
the old EPPA-only target remains available as a weaker comparator.
See `METRIC_EPPA_READABLE_TARGET.md` and PR #202 (checked/merged).

The reason to test this stronger assertion is precisely the scope of
the formalized *irreducible-structure faithfulness* theorem, not an
unrelated direct metric construction.

**Two proof mechanisms for D >= 2:**

1. Every complete monochromatic binary clique in the relational
   witness is irreducible. Thus the faithful witness's automorphism
   moves it into the embedded original A; reflection by the embedding
   preserves its colour and cardinality. PR #204 isolates
   irreducibility, PR #206 isolates exact cardinality transport.
2. For any symmetric **positive integer** edge costs, a walk of total
   weight 1 consists of one original weight-1 edge. For a partial
   distance structure of bound D >= 2, an unlabelled pair is assigned
   default cost D > 1, so canonical shortest-path completion cannot
   add a new distance-1 edge. PR #203 isolates this fact.

An isometric embedding A -> B gives the reverse clique-size inequality.
PR #207 formalizes the elementary numerical maximum-clique lemmas.

**D=1 warning, not an obstruction to the theorem.** Default cost D=1
would turn missing edges into 1-edges; therefore the no-new-unit-edges
statement for this completion is FALSE at D=1. Instead all genuine
1-bounded metrics are discrete, and the finite-set EPPA theorem
extends partial bijections on the same carrier. Choose B=A, preserving
its unit-clique size automatically. PR #205 formalizes this application
of the existing finite-set theorem. D=0 has a separately checked
identity-witness proof.

**Important scope guard:** The already verified class-level
locally-finite completion transfer, by itself, only promises *some*
completion in K. An arbitrary completion may add new distance-1
edges, so the extra clique equality is not automatic from the
class-level existential transfer alone. To obtain the stronger test,
explicitly choose the canonical shortest-path metric completion
in the final construction and preserve the irreducible-faithful
property of the intermediate relational witness. One can use the
checked restricted/tree-like theorem directly and invoke metric
amalgamation to discharge its bounded local obligations.

**Status:** these are independently auditable proof obligations.
None of the PRs above may be interpreted as a proof of the entire
all-D strengthened EPPA claim until the final derivation is checked.
