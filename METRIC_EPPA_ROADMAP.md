# Next regression: EPPA for finite integer metric spaces, uniformly in D

**Scope.** For every natural number D and every finite metric space A with
distances in {0,1,...,D}, construct a finite *metric* EPPA witness with the
same distance alphabet. Target both a human-readable ordinary-EPPA theorem
and, if the verified machinery makes it convenient, coherent EPPA.

**Trust status (2026-10-11).** The only code introduced so far is
`Examples/IntegerMetricBasic.lean`: mathematical vocabulary and
diameter-truncation lemmas. There is **no EPPA theorem** here yet.
Full CI and the axiom audit must pass before merging this first module.

## Chosen route

Use the already verified restricted/tree-like theorem `thm:maintree`
and the already verified locally finite completion transfer
`thm:mainstrong` (Theorem 1.6). The proof does *not* need
Proposition 11.3, which is a separate outstanding paper theorem.

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
   has fewer than d edges and involves at most d+1 <= D+1 vertices.
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

## Current next action

Wait for CI on the first vocabulary module; then implement the
finite distance-relation encoding, followed by weighted paths and
canonical shortest-path completion, before attacking strong
amalgamation and the locally-finite class interface.
