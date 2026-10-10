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


### Closed irreducible amalgamation bases (2026-10-10)

After PR #10 formalized actual free decompositions from any nonadjacent
pair in a finite irreducible-structure faithful E-complete witness,
and PR #11 excluded induced squares using two distinct components,
three additional CI-checked modules bridge to the eventual chordal
separator induction:

- `TreeLikeIrreducibleSeparator.lean`: a closed E-clique is an
  irreducible induced substructure (proved directly, avoiding a
  dependent rewrite through its closure).
- `TreeLikeMinimalClosed.lean`: inclusion-minimal separators are
  closed under all unary functions whenever irreducibles are E-cliques.
- `TreeLikeCliqueAmalgamationBase.lean`: if a minimal separator is
  also an E-clique, it is **already** an irreducible amalgamation base.

These results isolate the remaining genuinely graph-theoretic step:
`NoBadInducedCycles G → every minimal vertex separator is a clique`.
The classical proof uses two shortest induced paths through the two
components of the complement and concatenates them into a forbidden
induced cycle. Its arbitrary-length path argument is NOT yet formalized;
neither the full tree-amalgamation constructor nor `thm:maintree`
should be marked proved.


### Shortest induced paths through components (2026-10-10)

The following three modules passed their separate complete Lean CI runs
and axiom audits, and are integrated through the current PR:

- `TreeLikeShortestWalk.lean`: reachable vertices have a walk of
  minimum length, via `Nat.find`; minimum-length walks are simple
  paths, and edges between two nonconsecutive positions are excluded
  by constructing a shorter shortcut.
- `TreeLikeChordlessShortest.lean`: every reachable pair has a
  chordless (induced) path, by upgrading the shortest-walk properties.
- `TreeLikeComponentPaths.lean`: the graph induced on any connected
  component of G outside S has chordless paths between every pair
  of its vertices, with intermediate vertices necessarily remaining
  in that outside component.

These modules reduce the outstanding chordal clique-separator argument
to carefully connecting two such paths through distinct components
(and converting the resulting long induced graph cycle to the existing
`BadCycleSequence` API). The full clique-separator theorem, complete
`lem:cuts`, and `thm:maintree` are still **not** formalized.


### Joining induced paths (2026-10-10; PR #14)

After PR #13 added independently checked shortest chordless paths
inside a specified component of the complement of a separator, PR #14
integrates three further Lean modules from green CI branch
`tree-like-two-path-cycle` (`4cc9e248`):

- `TreeLikeChordlessReverse.lean`: the reverse of a chordless
  walk is chordless.
- `TreeLikeChordlessAppend.lean`: two chordless walks may be
  concatenated without creating chords provided all cross-support
  edges already belong to one of the constituent walks.
- `TreeLikeTwoPathCycle.lean`: two internally disjoint paths
  with a cross-edge locality condition assemble into an induced
  (chordless) cycle in `mathlib.SimpleGraph`.

**Not proved:** the cross-edge locality condition for the concrete
paths in distinct separator components; the translation of a
mathlib chordless cycle to our `BadCycleSequence`; the general
chordal minimal-separator clique theorem; the tree-amalgamation
induction of `lem:cuts`; or `thm:maintree`.


### Induced paths inside prescribed vertex subsets (2026-10-10)

`TreeLikeInducedAmbientPath.lean` proves that a chordless path chosen
in a Mathlib graph induced on a set T stays chordless and simple when
included in the original graph, with support still contained in T.
It also exposes the useful existence form: reachability of u,v in the
induced graph yields a chordless ambient path supported entirely in T.
This module passed a standalone full Lean build and axiom audit on
feature branch `tree-like-induced-ambient-path`. The related endpoint-
through-component construction and the full chordal clique theorem
remain separate proof obligations.


### Paths through different separator components (2026-10-10; PR #16)

Four more modules, each previously checked by the full Lean build and
axiom audit, are integrated:

- `TreeLikeCrossComponentEdges.lean` excludes additional graph edges
  between chordless paths supported (apart from their shared endpoints)
  in different outside components of a vertex separator;
- `TreeLikePathInteriorDisjoint.lean` proves these two paths have
  disjoint interiors and form a chordless Mathlib graph cycle;
- `TreeLikeComponentNeighborhoodPath.lean` constructs a chordless
  separator-to-separator path supported in a single specified outside
  component from endpoint-neighbor witnesses;
- `TreeLikeNonadjacentPathLength.lean` bounds from below the length
  of a walk between distinct nonadjacent endpoints by two.

The next required bridge is translating a long Mathlib chordless
cycle to our `BadCycleSequence` API (under active CI), followed by
proving the actual chordal minimal-separator clique theorem. Neither
`lem:cuts` nor `thm:maintree` has yet been proved in full.


### Chordal minimal-separator clique theorem (2026-10-10, PR #17)

The central graph-theoretic obstacle in `lem:cuts` has now been proved
by Lean on the feature branch `tree-like-chordal-minimal-clique`
(commit `03cec72d`, green complete CI and axiom audit), building on
PRs #13–#16:

- `TreeLikeCycleTranslation.lean`: converts a Mathlib `SimpleGraph.Walk`
  of length at least four carrying `IsCycle` and `IsChordless`
  certificates into our exact `Structure.BadCycleSequence`;
- `TreeLikeChordalMinimalClique.lean`: every inclusion-minimal vertex
  separator of a graph with no long induced cycles is a clique;
  the no-`BadCycleSequence` hypothesis for the distinguished E
  relation implies graph chordality; in unary-function structures
  with E-clique irreducibles, a minimal separator is both closed
  and irreducible.

PR #17 brings these exact proven modules onto the current `main`,
with an additional combined CI run before merging.

**Unfinished:** the induction on the number of vertices which
realizes a finite structure with chordal E-reduct as a substructure
of a *tree amalgamation of copies of A*. In particular, a complete
formal definition and construction of tree amalgamations, faithful
copies of A covering irreducibles, and the recursive free-amalgam
of two smaller witnesses remain to be built. The full `lem:cuts`
and `thm:maintree` MUST NOT be marked proved yet.


### Chordal free cuts, clique-tree certificates and the true `lem:cuts` hypotheses (2026-10-10)

The central graph result was merged as PR #17. Since that point:

- **PR #18 (merged, green Lean build and axiom audit):**
  `TreeLikeChordalCut.lean` proves the complete/noncomplete dichotomy.
  In the noncomplete case, it constructs a **proper free decomposition**
  whose *exact* common intersection is a closed irreducible substructure.
- **PR #21 (merged, green):**
  `TreeLikeCompleteIrreducible.lean` proves that an E-complete
  structure is irreducible even for languages with arbitrary
  set-valued functions.
- **Integration PR #26:** combines six further proof modules in one
  CI run to avoid conflicts between stacked PRs:
  - `TreeLikeInducedIrreducibles.lean`: irreducible-to-E-clique,
    looplessness, symmetry and absence of bad induced cycles
    pass to closed induced pieces; this uses exact transport of
    irreducibility across nested inductions.
  - `TreeLikeCliqueTree.lean`: by strong induction on the finite
    vertex count, a chordal structure satisfying those conditions
    admits a recursive certificate of **proper free amalgamation**
    from E-complete leaves over closed irreducible bases.
  - `TreeLikeInducedEmbeddings.lean`: the stronger paper hypothesis
    `EveryIrreducibleEmbedsIn act A B` also passes to closed pieces.
  - `TreeLikeEmbeddingCliqueBridge.lean`: this actual embedding
    hypothesis implies all irreducibles are E-cliques whenever E
    is Γ-fixed and complete in A.
  - `TreeLikeFaithfulEmbeddingBridge.lean`: derives the actual
    embedding hypothesis from irreducible-structure faithfulness
    using **previously formalized**
    `Faithful.automorphismInducedEmbedding` and
    `Faithful.embeddingInverseOnClosedSubset`.
  - `TreeLikeEmbeddingFactor.lean`: an optional general
    factorization of exact Γ-embeddings through an inclusion
    of images, respecting all set-valued function fibres.

**Scope of this milestone:** `CliqueTree E B` certifies a recursive
decomposition of B into E-complete pieces. It is **not** the paper's
tree amalgamation of full copies of A. Although the complete pieces
are irreducible and therefore embed into A under the paper's
hypothesis, Lean still needs an explicit construction of the
superstructure consisting of full A-copies, including the recursive
free-amalgamation/gluing over matching substructures of A and proof
that B embeds into it.

**Next proof obligations (in order):**
1. Equip each clique-tree leaf with a chosen embedding into A,
   using the newly hereditary local embedding hypothesis.
2. Define finite tree amalgamations of full A-copies, and prove the
   irreducible-bag coverage property for arbitrary irreducible
   substructures of such a tree.
3. Construct the glued A-copy superstructure recursively along a
   clique-tree certificate, retaining a structure embedding of B;
   this completes the actual `lem:cuts`.
4. Connect the completed lemma to the already formalized
   `lem:sparsen` trichotomy and iteration budget to prove
   `thm:maintree`, including coherence and forgetting E.

**Do not mark `lem:cuts` or `thm:maintree` formalized before
steps 1–4 are verified by Lean.** The integration PR #26 is likewise
not a `main` result until its own complete CI and axiom audit pass
and the PR is merged.


### Verified full-A tree machinery; precise remaining gap (2026-10-10, through PR #48)

**Authoritative update, superseding older progress notes above where they
say the chordal separator theorem or the full-A tree definition is still
missing.** All of the following have been merged into `main` after a
complete Lean build and the project-wide axiom audit:

- PRs **#17, #18, #21, #26**: the graph-theoretic chordal separator
  theorem, proper irreducible free cuts, induced-structure heredity, and
  recursive `CliqueTree E B` structural certificates.
- PRs **#27, #29**: `ACliqueTree act A E B` labels every complete
  leaf with an **actual exact embedding into A**. The distinguished
  E-relation is automatically loopless and symmetric under the full
  irreducible-embedding hypothesis; these are not extraneous hypotheses
  added to manuscript `lem:cuts`.
- PR **#34**: the image of any exact Γ-structure embedding is closed
  under arbitrary set-valued functions, and intersections of closed
  sets are closed.
- PRs **#38, #41**: explicit construction of finite amalgam carriers,
  genuine amalgam *structures* with all relations and set-valued
  functions, **exact embeddings of both source structures**,
  alignment of different Γ-language components, and the manuscript's
  **literal `TreeAmalgamation` inductive definition** whose basic
  pieces are **full copies of A**, not merely clique bags.
- PR **#45**: the constructed amalgam has a genuine
  `FreeDecomposition` whenever the two sources are proper. More
  generally `FreeCover` works even for degenerate attachments and
  implies that every irreducible closed substructure lies entirely
  in one source side.
- PR **#48**: Γ-isomorphic transport of irreducibility; the exact
  closed image of an irreducible Γ-embedding is irreducible;
  lifting a full-A extension through an embedded side; and, most
  importantly, the **fully Lean-proved**
  `TreeAmalgamation.everyIrreducibleExtendsToA`:

  > Every closed irreducible induced substructure of any recursive
  > tree amalgamation of full copies of A is contained in the
  > image of a genuine Γ-structure embedding of the *whole* A.

  This includes nontrivial language permutations, arbitrary set-valued
  functions and gluing along an entire side. PR #48 also integrates
  finiteness of full-A tree amalgamations when A is finite.

**The paper's `lem:cuts` is still OPEN.** The new theorem above is
the *observation used in its induction*, not the lemma's conclusion.
The remaining core task is to show that the existing
`ACliqueTree act A E B` certificate is **realized inside a
`TreeAmalgamation act A H`**, with an exact Γ-embedding
`B ↪ H`. A precise proof plan is recorded on PR #47:

1. A leaf embeds in A directly; use `TreeAmalgamation.singleton`.
2. In a proper free-decomposition node, recursively embed both closed
   induced sides of B into full-A tree amalgamations H₁,H₂.
3. The exact closed irreducible intersection embeds irreducibly into
   each Hᵢ. Apply PR #48's extension observation to factor each
   base embedding through a **full embedded copy of A** in Hᵢ.
4. Glue H₁,H₂ on these embeddings of the exact common base, using
   `generalAmalgamStructure` and `TreeAmalgamation.glue`.
5. **Still to prove:** the genuine pushout/universal-property
   embedding of the original freely decomposed B into this glued
   target. It must show injectivity (the only cross-identifications
   arise from the exact common base), **relation reflection**, and
   **equality** of all set-valued-function fibres. Here one uses
   `FreeDecomposition.rel_local` and
   `FreeDecomposition.func_cross_empty`; merely a homomorphism or
   a set-theoretic vertex inclusion would NOT suffice.

Feature PRs **#49** (exact embeddings of the common closed base),
**#50** (unique/injective carrier gluing), and **#51** (pointwise
identification of the factored base embeddings) are preliminary
steps toward item 5 and are **not authoritative until their own
CI passes and they are integrated**.

After the exact `lem:cuts` realization is Lean-proved, the further
work to finish `thm:maintree` is to connect it to the already
formalized `lem:sparsen` iteration, including preservation of EPPA,
the coherence condition, the required bound, and forgetting the
added E-relation. **Do not call either theorem proved until this
code compiles without `sorry` and passes the standard axiom audit.**
