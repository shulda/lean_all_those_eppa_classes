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
| Proposition `prop:infinite_languages`: finite relabelling orbit in an arbitrary relational language | `AllThoseEPPA/Relabelling.lean`, `AllThoseEPPA/InfiniteRelational.lean`; `AllThoseEPPA.InfiniteRelational.finiteOrbitRelationalStructuresHaveCoherentEPPA` | **Formalized** | Uses an equivalent direct finite profile language with the original group Γ, rather than adjoining all paper symbols and then invoking `lem:redundant_groups`. The finite witness and coherent transfer through `T` and `U` are checked. |\n| Unary functions / Proposition `prop:eppafunctions` | — | **Current target** | The required infinite-language relational proposition is now green. |
| Irreducible-structure faithfulness | — | Planned | Regression target: finite 3-uniform hypergraphs. |
| Restricted / locally tree-like construction | — | Planned | Regression target: finite integer-valued metric spaces with distances `{0,...,D}`. |
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
