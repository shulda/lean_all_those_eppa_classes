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
| Restricted / locally tree-like construction / Theorem `thm:maintree` | `AllThoseEPPA/TreeLikeDescent.lean`, `TreeLikeEdgeBudget.lean`, `TreeLikeClosedProjection.lean` (merged); `TreeLikeClique.lean`, `TreeLikeEdgeCut.lean`, `TreeLikeFaithfulClique.lean`, `TreeLikeFaithfulGraph.lean`, `TreeLikeGraphInterface.lean`, `TreeLikeInducedCycles.lean` (work branch) | **In progress** | Iteration counting and closed projections are on `main`. The work branch tackles the structural and graph-interface ingredients of `lem:cuts`; still missing the chordal clique-separator theorem, actual tree-amalgamation construction, clique-relation expansion/reduct and the fully iterated witness theorem. |
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
and the axiom audit succeeded. The separate follow-up PR #4 adds the
fact that exact unary-function projections carry closed subsets to
closed images, allowing projections of genuine substructures to be
iterated.

**Critical next dependency**: `lem:cuts`, which upgrades a finite
chordal E-reduct whose irreducible substructures embed into the distinguished
clique A to a substructure of a tree amalgamation of copies of A.
The proof needs a rigorous chordal clique-separator argument compatible
with unary-function closures; it is not implied by the existing
cycle-sparsening trichotomy alone.


### Structural progress toward `lem:cuts` (2026-10-09)

The next proof layer starts with an elementary, but important, distinction:
a graph-theoretic separator is not automatically a *closed* separator for
set-valued unary functions. A correct route must both establish that the
separator is the closure of an E-clique and show that the two sides stay
closed under all functions.

The following Lean modules are under development in the work branch
`tree-like-induced-cycle-bridge`; they should be considered formally
verified only after its complete Lean build and axiom audit succeed:

- `TreeLikeClique.lean`: the closure of an E-clique is irreducible,
  regardless of function arities; when every irreducible substructure is
  an E-clique, it follows that the closure of a clique is a clique.
  Every realized relation tuple and unary-function value is then E-local.
- `TreeLikeEdgeCut.lean`: a closed graph separator without edges between
  exclusive sides induces a genuine free decomposition, assuming unary
  functions and E-cliquish irreducibles. The proof checks relation tuples,
  function closure of both sides, and the empty cross-function clause.
- `TreeLikeFaithfulClique.lean` and `TreeLikeFaithfulGraph.lean`: connect
  these hypotheses to the *existing* irreducible-structure faithful
  EPPA construction. In particular, E is loopless and symmetric in the
  entire faithful witness when E is fixed and complete on the copy of A.
- `TreeLikeGraphInterface.lean`: expose the distinguished E-reduct as a
  `mathlib.SimpleGraph` and identify the two notions of E-clique.
- `TreeLikeInducedCycles.lean`: lift a bad induced cycle of a closed
  induced substructure to the ambient structure. This transports the
  good alternative of `lem:sparsen` to the graph-theoretic task.

**What is NOT proved:** `lem:cuts` itself. In particular, Mathlib's
current pinned graph library defines chordless walks, but does not
provide a ready-made theorem that finite graphs without induced cycles
of length at least four have clique minimal separators / a clique tree.
This is the next substantial graph-theoretic obligation, followed by
building a tree amalgamation of copies of A and then completing
`thm:maintree`. Do not state the full theorem until those obligations
have closed in Lean.
