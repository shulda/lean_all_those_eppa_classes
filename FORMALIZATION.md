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
| Section 3: graph warm-up | — | Planned | Next nontrivial construction/regression target. |
| General relational construction | — | Planned | Leads to the unrestricted relational theorem. |
| Unary functions | — | Planned | |
| Irreducible-structure faithfulness | — | Planned | Regression target: finite 3-uniform hypergraphs. |
| Restricted / locally tree-like construction | — | Planned | Regression target: finite integer-valued metric spaces with distances `{0,...,D}`. |
| Hrushovski-construction application | — | Deferred | Deliberately postponed until the general machinery is complete and stable. |
