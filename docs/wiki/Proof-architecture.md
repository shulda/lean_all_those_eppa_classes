# Proof architecture of the formalized EPPA constructions

This is a mathematical roadmap, not a tactic-by-tactic transcription.
Use the [statement crosswalk](Published-statements.md) first: a
verified implementation step does not enlarge the scope of its stated
theorem automatically.

## Dependency roadmap

```text
Finite set coherent extensions and finite partial equivalences
  ↓
Relational valuations over F₂; coherent symbol/vertex actions
  ↓
Finite relabelling-profile reduction for infinite languages
  ↓
Unary set-valued functions: valuations on one-point closures
  ↓
Faithful valuation refinement (irreducible substructures)
  ↓
Unrestricted coherent faithful EPPA (Theorem 1.1)

Faithful EPPA + finite cycle sparsening
  ↓
Chordal/cut decomposition; trees of full A-copies
  ↓
Restricted/tree-like EPPA (Theorem 1.2)
  ↙                                    ↘
Finite forbidden family + ambient N     Locally finite automorphism-
  ↓                                     preserving completions
Herwig–Lascar theorem (1.5)              ↓
                                      Local subclass transfer (1.6)

Independent kernel/strong-amalgamation argument
  ↓
Proposition 11.3, ordinary iff injective completion
```

## Relational valuation and symbol relabeling

The relational stage uses valuations with binary flip data over
the additive group of the two-element field. What must be
proved is not only the existence of a witness but a *coherent*
choice of permutation extensions, respecting the language-symbol
group component and composition on coherent partial triples.
Relevant files: [`RelationalWitness.lean`](../../AllThoseEPPA/RelationalWitness.lean),
[`F2Completion.lean`](../../AllThoseEPPA/F2Completion.lean),
[`RelationalExtension.lean`](../../AllThoseEPPA/RelationalExtension.lean).

For infinitely many symbols, finite Γ-orbit of the relabelled
input permits coding only a finite family of realised profiles.
Encoding/decoding and coherent extension transfer then avoid
assuming Γ is finite.
See [`InfiniteRelational.lean`](../../AllThoseEPPA/InfiniteRelational.lean)
and [`Relabelling.lean`](../../AllThoseEPPA/Relabelling.lean).

## Unary functions and faithfulness

For unary set-valued functions, the closure of a single vertex
provides the support on which valuation information must agree.
The code separates abstract finite presentations from the
physical valuation signature carried by a witness point;
transport must not depend on a chosen presentation.
See [`UnaryFunctions.lean`](../../AllThoseEPPA/UnaryFunctions.lean)
and [`UnaryFunctionsCoherence.lean`](../../AllThoseEPPA/UnaryFunctionsCoherence.lean).

Faithfulness adds valuation labels against *bad* irreducible
substructures of an existing witness. A generic collection of
valuation points prevents any bad irreducible from surviving
as a substructure not movable into the source copy. It is
important that this construction preserves both ordinary EPPA
and coherent composition of extensions.
See [`Faithful.lean`](../../AllThoseEPPA/Faithful.lean),
[`FaithfulProposition.lean`](../../AllThoseEPPA/FaithfulProposition.lean)
and [`UnrestrictedFaithfulEPPA.lean`](../../AllThoseEPPA/UnrestrictedFaithfulEPPA.lean).

## Restricted construction and tree-like local structure

The cycle-sparsening step introduces a controlled parity/flip
construction. Its verified trichotomy controls vertices, edges
and induced cycles while retaining a projection that is a
homomorphism-embedding and a coherent, faithful EPPA witness.
See [`CycleSparseningTheorem.lean`](../../AllThoseEPPA/CycleSparseningTheorem.lean).

Iterated sparsening bounds local complexity. Chordal separator
and clique-tree arguments then place every sufficiently small
**function-closed** substructure in a literal recursive tree
amalgamation of **entire original source copies**, via
homomorphism-embeddings. The proof initially adjoins a fresh
complete binary relation E fixed by Γ, then removes E after
performing the fixed-E construction. This ensures that the public
theorem does not impose an extra relation symbol on users.

The important endpoints are
[`TreeLikeUnrestrictedMaintree.lean`](../../AllThoseEPPA/TreeLikeUnrestrictedMaintree.lean)
and the supporting
[`TreeLikeFixedEFullMainTheorem.lean`](../../AllThoseEPPA/TreeLikeFixedEFullMainTheorem.lean).
The code may use larger safe finite bounds than the paper;
the public existential local-control statement does not require
an optimal bound.

## Herwig–Lascar and locally finite completion

For the forbidden-family theorem, the restricted construction
is combined with tree amalgamations whose copies of the source
can be homomorphism-embedded into the ambient model N. A forbidden
configuration in the finite constructed witness would map into
N, contradicting N's membership in `Forb(F)`. The exact
forbidden notion is **homomorphism-embedding**.
See [`TreeLikeInfiniteCopiesTheorem.lean`](../../AllThoseEPPA/TreeLikeInfiniteCopiesTheorem.lean)
and [`HerwigLascarTheorem.lean`](../../AllThoseEPPA/HerwigLascarTheorem.lean).

For locally finite classes, small trees have K-completions by
amalgamation. The locally finite hypothesis yields a global
automorphism-preserving strong completion. The resulting
automorphism lift transports ordinary and coherent EPPA.
See [`StrongCompletionLocallyFiniteStep.lean`](../../AllThoseEPPA/StrongCompletionLocallyFiniteStep.lean)
and [`StrongCompletionManuscriptSubclass.lean`](../../AllThoseEPPA/StrongCompletionManuscriptSubclass.lean).
Here the **AP-only** theorem is the closer counterpart of the
published transfer theorem; the facade also offers a convenient
hereditary-SAP specialization.

Proposition 11.3 is a **different** argument: an ordinary
completion can be upgraded to a globally injective one under
heredity and strong amalgamation. A minimal-kernel/quotient
and two-sided gluing argument underlies
[`StrongCompletionProposition113.lean`](../../AllThoseEPPA/StrongCompletionProposition113.lean).
No automorphism-preserving lift follows from this proposition alone.

## Large d-closure application

The rooted k-orientation development applies the faithful coherent
machinery twice, first in a successor encoding and then with a
generally **nontrivial** action of the first witness's automorphism
group on auxiliary symbols. It constructs an actual finite
rooted k-orientation and verifies the **full all-positive-arity**
d-structure, genuine original-source embedding, coherent partial
extension selector and faithfulness.
See [`RootedKOrientationDFinalEPPA.lean`](../../AllThoseEPPA/Applications/KOrientations/RootedKOrientationDFinalEPPA.lean)
and [Applications](Applications.md).

This implementation only covers input orientations satisfying
`HasReachableRoots k`; it must not be used to certify the
unqualified published Theorem 12.9.
