# Formalization status

This file is the repository-side map between the paper and Lean.  The
authoritative manuscript lives in the private Overleaf mirror.

**Status meanings**

- **API formalized**: the mathematical notion has a Lean definition and the
  project builds with it.
- **Formalized**: the relevant statement and proof are checked by Lean on
  `main`.
- **Planned**: not yet part of the trusted formalization.

GitHub Actions runs `lake build` and an axiom audit on every push and pull
request.  A result is called **Formalized** here only after that CI run is
green.

| Paper item | Lean declaration / file | Status | Notes |
| --- | --- | --- | --- |
| Languages with Γ_L and arities | `AllThoseEPPA/Language.lean` | API formalized | Symbols are indexed by arity, so preservation of arity by Γ_L is encoded in the type. |
| Set-valued structures | `AllThoseEPPA/Structure.lean` | API formalized | Function symbols are interpreted as maps from tuples to sets, as in the paper. |
| Homomorphisms and embeddings | `AllThoseEPPA/Map.lean` | API formalized | Homomorphisms use inclusion on function values; embeddings use equality. |
| Substructures | `AllThoseEPPA/Substructure.lean` | API formalized | Closed subsets induce substructures. |
| Partial isomorphisms and coherent triples | `AllThoseEPPA/PartialIso.lean` | API formalized | Equality of mathematical partial maps uses `PartialEquiv.EqOnSource`, not raw Lean equality outside the domain. |
| EPPA / coherent EPPA witness API | `AllThoseEPPA/EPPA.lean` | API formalized | Extension is stated along an explicit embedding ψ. |
| Proposition `prop:setcoherence`: finite sets have coherent EPPA | `AllThoseEPPA.finiteSetsHaveCoherentEPPA` | **Formalized** | The canonical extension matches unused points in increasing order; the order is chosen internally for an arbitrary finite type. |
| Lemma `lem:graphs:auto` / finite graphs have EPPA | `AllThoseEPPA/Examples/GraphWitness.lean`, `AllThoseEPPA/Examples/GraphExtension.lean`; `AllThoseEPPA.Graph.finiteGraphsHaveEPPA` | **Formalized** | Explicit valuation witness, generic embedding, flip consistency, witness automorphism and extension are checked. |
| Lemma `lem:graphs:coherence` and Proposition `prop:graphs` | — | Intentionally skipped | The graph section has served its purpose as an API warm-up; coherence is deferred unless later work needs it. |
| Proposition `prop:relstructures`: finite relational structures have coherent EPPA | `AllThoseEPPA/RelationalWitness.lean`, `AllThoseEPPA/F2Completion.lean`, `AllThoseEPPA/RelationalExtension.lean`; `AllThoseEPPA.Relational.finiteRelationalStructuresHaveCoherentEPPA` | **Formalized** | The full affine/𝔽₂ valuation construction is checked, including extensionality of partial maps and coherent composition. |
| Proposition `prop:infinite_languages`: finite relabelling orbit in an arbitrary relational language | `AllThoseEPPA/Relabelling.lean`, `AllThoseEPPA/InfiniteRelational.lean`; `AllThoseEPPA.InfiniteRelational.finiteOrbitRelationalStructuresHaveCoherentEPPA` | **Formalized** | Uses an equivalent direct finite profile language with the original group Γ, rather than adjoining all paper symbols and then invoking `lem:redundant_groups`. The finite witness and coherent transfer through `T` and `U` are checked. |
| Unary functions / Proposition `prop:eppafunctions` | `AllThoseEPPA/UnaryFunctions.lean`, `AllThoseEPPA/UnaryFunctionsCoherence.lean`; `AllThoseEPPA.UnaryFunctions.finiteOrbitUnaryStructuresHaveCoherentEPPA` | **Formalized** | Uses finite abstract valuation presentations only to prove realizability and finiteness, then quotients to presentation-independent physical valuation signatures. The finite witness, generic embedding, lifted automorphisms, extension square and coherent composition are checked. |
| Irreducible-structure faithfulness / Proposition `prop:faithful` | `AllThoseEPPA/FaithfulProposition.lean`; `AllThoseEPPA.Faithful.faithfulWitness_proposition` (and supporting `Faithful*.lean` files) | **Formalized** | Finite, irreducible-structure faithful coherent extension of an arbitrary finite EPPA witness; includes projection as a homomorphism-embedding. |
| Unrestricted construction / Theorem `thm:nreppa` | `AllThoseEPPA/UnrestrictedFaithfulEPPA.lean`; `AllThoseEPPA.Faithful.finiteOrbitUnaryStructuresHaveFaithfulCoherentEPPA` | **Formalized** | Finite-relabel-orbit unary-function structures admit finite irreducible-structure faithful coherent EPPA witnesses. |
| Induced-cycle sparsening / Lemma `lem:sparsen` | `AllThoseEPPA/CycleSparseningTheorem.lean`; `AllThoseEPPA.Sparsening.cycleSparseningLemma`, `cycleSparseningLemma_coherent` | **Formalized** | Finite witness, coherent EPPA, irreducible-structure faithfulness, homomorphism-embedding projection, and the full vertex/edge/induced-cycle trichotomy for arbitrary subsets. |
| Restricted / locally tree-like construction / Theorem `thm:maintree` | `AllThoseEPPA/TreeLike*.lean` (PRs #3–#9) | **In progress** | Checked: finite sparsening descent, exact closed projections, clique closure, graph component-to-free-decomposition cut, faithful E graph, induced-cycle transport and the explicit square obstruction. PR #9 contributes existence of inclusion-minimal vertex separators and closure of two-sided separators. Not yet checked: minimal separator → two-sided neighbors → clique, tree-amalgamation constructor, E expansion/reduct, full iterated EPPA. |
| Hrushovski-construction application | — | Deferred | Deliberately postponed until the general machinery is complete and stable. |


### Foundation audit note

On 2026-10-06 the start of the general relational construction exposed that the paper requires relation symbols to have positive arity, while the initial Lean `Language` allowed nullary relations. The Lean API was corrected by adding `Language.relArity_pos`. No manuscript correction was needed: the paper already states the requirement explicitly in the background section.


### Infinite-language proof note

The Lean proof of Proposition `prop:infinite_languages` compresses directly to
a finite profile language whose symbols are coded by a member of the finite
relabelling orbit of `A` together with an injective tuple.  Different codes
may name the same profile; this redundancy is harmless.  The original group
`Γ` acts directly on these codes, so the formal proof does not need the
paper's intermediate language `M = M' ∪ L` nor a separate application of
Lemma `lem:redundant_groups`.

The proof still formalizes the substantive `T/U` mechanism: profile encoding
is functorial on embeddings, decoding is functorial on embeddings,
`U(T(A)) = A` at the relational level, partial automorphisms lift to `T(A)`,
and coherent automorphism extensions decode back to the original language.


### Unary-function proof note

The Lean proof of Proposition `prop:eppafunctions` separates finite
presentation data from the mathematical valuation carried by a witness
vertex.  An abstract valuation presentation consists of a relabelled copy of
a one-point closure together with its embedding into the relational base
witness.  Its `ValuationSignature` records only the resulting support and
unary-function graph inside the base witness.  The final witness uses realised
physical signatures, so transport by a base automorphism is independent of
the chosen presentation.  Restriction to one-point closures and transport
commute, which makes both extension of the generic copy and coherent
composition functorial.


### Merge checkpoint and restricted EPPA work (2026-10-09)

Pull request [#2](https://github.com/shulda/lean_all_those_eppa_classes/pull/2)
merged `irreducible-faithfulness` and `cycle-sparsening` into `main` at
commit `35de7e9`. Full Lean CI and the axiom audit succeeded on that merge.
This closes Proposition `prop:faithful`, Theorem `thm:nreppa`, and Lemma
`lem:sparsen`. The hypergraph regressions `Hypergraph3.eppa` and
`Hypergraph3.eppaK4Free` were separately verified on branch
`hypergraph3-k4-free-eppa`; they are not yet imported on `main`.

The next paper target is `thm:maintree` (Section `sec:maintree`). Its
iteration budget in the manuscript is
`(n-1) + n * (n choose 2) + 1`, counting undirected edges. In Lean,
`Sparsening.EdgePairs` counts *ordered* edges. A uniformly safe bound
is therefore `Q=n*n`, giving `n*(Q+1)` steps in the first
formalized counting argument. This larger finite bound is sufficient
for the theorem, although optimizing it to the manuscript's formula
can be revisited later.

The independently checkable rank argument is in
`TreeLikeDescent.lean`: the rank `(vertices-1)*(Q+1)+(Q-edges)`
strictly increases at every step not satisfying the no-cycle alternative
of the trichotomy, and stays below `n*(Q+1)`. The concrete directed
edge-budget estimate is in `TreeLikeEdgeBudget.lean`. Both modules were
merged into the trusted `main` branch through PR #3, after full Lean CI
and the axiom audit succeeded. PR #4 also merged and verified that exact
unary-function projections carry closed subsets to closed images, allowing
projections of genuine substructures to be iterated.

**Critical next dependency**: `lem:cuts`, which upgrades a finite
chordal E-reduct whose irreducible substructures embed into the distinguished
clique A to a substructure of a tree amalgamation of copies of A.
The proof needs a rigorous chordal clique-separator argument compatible
with unary-function closures; it is not implied by the existing
cycle-sparsening trichotomy alone.


### `lem:cuts` structural checkpoint and graph bridge (2026-10-09)

PR #5 was merged after a full Lean build and axiom audit (merge `819bb4d`).
The project now checks:

- `TreeLikeClique.lean`: the closure of any E-clique is an irreducible
  substructure, including for set-valued functions of arbitrary arity;
  closures of cliques remain cliques when all irreducibles are E-cliques.
- `TreeLikeEdgeCut.lean`: a closed graph separator of a unary-function
  structure, with no E-edges across the exclusive sides, gives a genuine
  `Structure.FreeDecomposition`, including function closure.
- `TreeLikeFaithfulClique.lean`, `TreeLikeFaithfulGraph.lean`: when E is
  fixed and complete on A, irreducible-structure faithfulness forces E
  to be a symmetric, loopless graph throughout the witness and proves the
  clique hypothesis required for the cut lemma.

The graph-theoretic interface is provided by PR #6, bringing two
already independently CI-checked modules onto the current `main`:

- `TreeLikeGraphInterface.lean`: converts E into a real Mathlib
  `SimpleGraph` and identifies our E-clique predicate with its
  `SimpleGraph.IsClique` predicate.
- `TreeLikeInducedCycles.lean`: lifts a bad induced cycle from a
  closed induced substructure into the ambient structure, preserving
  the inclusion of the cycle carrier. This supplies the no-induced-cycle
  branch of `lem:sparsen` to the chordal graph argument.

**Not proved:** the crucial finite graph-theoretic assertion that a
chordal graph has suitable clique separators, the extension of the
substructure to a tree amalgamation of copies of A, and the entire
restricted theorem `thm:maintree`. The graph result is a new proof
obligation; Mathlib at the pinned version has `Walk.IsChordless`
but no convenient all-in-one chordal clique-separator theorem.


### Finite graph-separator progress (2026-10-09, PRs #7–#9)

The following components and their dependencies have passed independent
complete Lean builds with axiom audits, and PR #9 integrates the checked
files onto the latest main:

1. `TreeLikeSquareObstruction.lean` (merged PR #7): four distinct
   vertices x-a-y-b-x with nonedges x-y and a-b form an actual
   `BadCycleSequence`, so no chordal E-reduct admits them.
2. `TreeLikeComponentCut.lean`, `TreeLikeComponentFree.lean` (merged
   PR #8): an outside connected component yields a cut whose sides
   cover the graph and have no cross edges. If S is closed and at least
   two outside components remain, it constructs a *genuine*
   `Structure.FreeDecomposition` of the irreducible-faithful witness.
3. `TreeLikeNeighborSeparator.lean`, `TreeLikeMinimalSeparator.lean`
   (PR #9): for any two distinct nonadjacent vertices of a finite
   graph, deleting the neighbors of one separates them. Minimizing the
   cardinality of a separating vertex set using `Nat.find` produces an
   inclusion-minimal separator.
4. `TreeLikeFunctionEdge.lean` (PR #9): if x-y is an E-edge and z is
   in a function value at the constant tuple x, then z-y is an E-edge
   unless z=y. This uses irreducibility of the closure of the E-tuple.
5. `TreeLikeTwoSidedClosure.lean` (PR #9): if every vertex of S has
   a neighbor in each of two **distinct** components of G\\S, then S
   itself is closed under all unary functions. In particular, *once*
   inclusion-minimality is shown to force that two-sided neighbor
   property, the proof need not pass to the closure of the separator.

The remaining chordal-graph obligations are substantive: for an
inclusion-minimal separator of u and v, show each separator vertex has
neighbors in both endpoint components; then show the separator is a
clique by combining induced paths through the two components into an
induced cycle. The already checked four-cycle lemma is the smallest
case. After this, implement a genuine tree amalgamation and finish the
restricted witness construction `thm:maintree`.

**Do not call `lem:cuts` or `thm:maintree` proved:** these exact
graph/path and tree-amalgamation proof obligations remain open.


### Completed free-decomposition descent (2026-10-10)

The coherent structural step following the already-merged separator
infrastructure is implemented in:

- `TreeLikeWalkClosure.lean`: adjacency-closed subsets of a graph are
  closed under all graph walks and reachability.
- `TreeLikeEssentialNeighbors.lean`: inclusion-minimal u-v separators
  meet both u and v endpoint components by adjacency at every separator
  vertex; this uses the previous adjacency-closure result.
- `TreeLikeTwoSidedFree.lean`: two outside components and two-sided
  separator adjacency automatically furnish a concrete
  `Structure.FreeDecomposition` of a faithful witness.
- `TreeLikeMinimalFree.lean`: for any two distinct nonadjacent vertices
  of the E-reduct of a finite faithful EPPA witness, select a minimal
  separator and construct a concrete free decomposition of the whole
  witness. The existence proof lies in Prop and the actual data object
  is obtained by Classical.choice, avoiding invalid Prop-to-Type
  elimination.

Each module passed complete Lean CI and the standard axiom audit on the
prior development branch; the combined PR must also pass its own CI.
**The full `lem:cuts` is not proved.** The missing implication is that
an inclusion-minimal separator is an E-clique in a chordal graph,
followed by the recursive tree-amalgamation construction.
