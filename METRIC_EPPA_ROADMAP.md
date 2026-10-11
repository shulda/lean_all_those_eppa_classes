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
- PR #192: `IntegerMetricWalkSupport.lean`, candidate finite-vertex support
  bound for every shortcut (at most D vertices); **CI pending**.


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

1. Complete the finite walk-support cardinality proof in PR #192 and
   integrate only after green complete Lean CI + axiom audit.
2. For a locally consistent partially distance-coloured Γ-structure B,
   define its *symmetric* direct-cost matrix: use its unique positive
   edge label when specified; otherwise use the default cost D.
   Prove that automorphisms of B preserve this matrix exactly, hence
   preserve the canonical shortest-path metric; this is the
   automorphism-preserving (and coherent) completion interface.
3. Prove that a B-structure whose substructures of size at most
   `max D 2` admit ordinary K-homomorphism-embedding completions
   has no loops, no asymmetric/conflicting colours, and no shortcut
   shorter than any old labelled edge. Use the finite support
   of a witness from (1), and triangle inequalities after mapping
   *individual old edges* into a metric completion. **Do not assume
   that the local completion is globally injective.**
4. Show any tree amalgamation of whole copies of a D-metric A has
   a D-metric completion preserving all old distances. One route:
   establish hereditary strong amalgamation for the metric class
   using shortest-path amalgams; alternatively derive exactly
   the needed tree-case lemma and use the restricted-EPPA theorem
   directly. Do not duplicate the main construction.
5. Instantiate the checked Theorem 1.6 transfer (or the equivalent
   direct `thm:maintree` interface) and conclude a self-contained
   ordinary/coherent EPPA statement for all D>0; join the already
   checked D=0 base case. The reader-facing statement must be about
   finite isometric embeddings and extension of partial isometries.

**Small-bound note.** For a direct edge d≤D shortened by a weighted
walk, its total walk cost is <d and every step costs ≥1. Hence the
number of steps is <d and the visited-vertex set has cardinality
at most d≤D. The separate `max D 2` includes pair-consistency
witnesses even when D=1. No optimisation of D beyond this is needed.
