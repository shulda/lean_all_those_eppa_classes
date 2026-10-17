# Mathematical definitions and their Lean interpretations

This page inspects the actual *logical content* of the definitions,
not just their Lean names. Checked at
[`d85fda061d0b`](https://github.com/shulda/lean_all_those_eppa_classes/commit/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d).
All types discussed below can be finite without requiring a chosen enumeration.

## Γ-languages and structures

[`Language.lean`](../../AllThoseEPPA/Language.lean) has arity-indexed
relation and function symbols `L.RelSymbol n` and `L.FuncSymbol n`.
A field `relArity_pos` excludes nullary relations. Instances
`L.HasUnaryFunctions` restrict all function symbols to arity 1,
but allow relations of every positive arity.

`L.Action Γ` assigns a group action to each arity's symbols,
preserving symbol kind and arity. It need not be trivial; this is
crucial in the Herwig–Lascar theorem and orientation reconstruction.

[`Structure.lean`](../../AllThoseEPPA/Structure.lean) interprets a
relation symbol as a predicate on `Fin n → V` and a function symbol
as a map `(Fin n → V) → Set V`. Thus functions are **set-valued**,
possibly undefined/empty or multiple-valued, not ordinary total
functions. Singleton-valued functions require an application-specific
encoding when necessary.

## Maps, substructures, and irreducibility

[`Map.lean`](../../AllThoseEPPA/Map.lean):

- A Γ-homomorphism records a language component `lang : Γ`, vertex
  map, forward implication for relations, and inclusion of the
  image of each function-value set.
- A Γ-embedding additionally requires injectivity, *equivalence*
  for relations, and *equality* for images of function-value sets.
- A Γ-homomorphism-embedding (in
  [`Irreducible.lean`](../../AllThoseEPPA/Irreducible.lean)) is a
  homomorphism that is an exact embedding on every closed irreducible
  substructure of its domain. It need not be globally injective.

Substructures are induced on subsets **closed under function
values**; closure is not merely graph-theoretic adjacency.
`Structure.IsIrreducible` means there is no decomposition into
two proper function-closed sides with all relation tuples on one side
and every function tuple crossing sides having an empty value.
This is the free-amalgamation notion of irreducibility.

## Partial isomorphisms and EPPA

A [`PartialIsomorphism`](../../AllThoseEPPA/PartialIso.lean)
has function-closed source and target, a partial equivalence of
their vertex sets, and a Γ-language component. Equality of
mathematical partial maps is `PartialIsomorphism.Equivalent`:
the language components agree and the vertex partial equivalences
have the same source and agree *on* that source. This avoids
comparing irrelevant auxiliary values outside a partial map's
domain.

A coherent triple `(f,g,h)` satisfies
`target(f)=source(g)` and `h=g∘f` as partial maps.
This convention is **not** an arbitrary pair of partially composable
maps with unmatched source and target.

For an embedding `ψ : A ↪ B`, the predicate
[`Structure.ExtendsAlong`](../../AllThoseEPPA/EPPA.lean)
requires a total automorphism `G` of B to satisfy

`G.lang * ψ.lang = ψ.lang * p.lang`

and `G(ψ(x)) = ψ(p(x))` for every x in the domain of p.
Consequently `IsEPPAWitness act ψ` is truly quantified over all
partial automorphisms of A and over total automorphisms of the
*same finite witness B*, including language-label compatibility.

`IsCoherentEPPAWitness` is existence of a *single selection*
`p ↦ G_p` of extensions that is invariant under
`Equivalent` and satisfies `G_h = G_g ∘ G_f` on every
coherent triple. This is stronger than independently extending
each partial automorphism.

## Irreducible-structure faithfulness

[`Structure.IsIrreducibleStructureFaithful act ψ`](../../AllThoseEPPA/Irreducible.lean)
states that for **each** function-closed irreducible induced
substructure S of B there is a Γ-automorphism G of B such that
`G(S) ⊆ ψ(A)`. The automorphism may depend on S; the definition
does not demand that B itself is irreducible, nor that *all*
irreducibles lie literally in the distinguished copy.

This is the property used to preserve classes forbidding finite
irreducible configurations.

## Forbidden configurations and completions

[`FiniteForbiddenFamily.Avoids`](../../AllThoseEPPA/HerwigLascarForbiddenFamily.lean)
forbids homomorphism-embeddings of finite forbidden structures.
It does **not** mean absence of an ordinary homomorphism or merely
absence of an induced copy.

[`HasLocallyFiniteAutomorphismPreservingCompletion`](../../AllThoseEPPA/StrongCompletionLocallyFiniteStep.lean)
quantifies, for each fixed finite pair A and B₀, some bound n
and all finite candidate structures B satisfying three hypotheses:
every irreducible substructure homomorphism-embeds into A,
B homomorphism-embeds into B₀, and every closed at-most-n-vertex
substructure has an ordinary K-completion. The conclusion supplies
an **automorphism-preserving strong** K-completion of B.

[`AutomorphismPreservingStrongCompletion`](../../AllThoseEPPA/AutomorphismPreservingCompletion.lean)
adds an injective homomorphism-embedding into an irreducible target
and a composition-preserving, Γ-compatible lift of all source
automorphisms. By contrast, [Proposition 11.3](Published-statements.md)
only upgrades ordinary to injective completions: it does not
automatically supply those automorphism lifts.

## Remaining semantic checks

This audit has read the foundational declarations, but does not
claim an independently constructed equivalence between every
paper definition and its representation in Lean. Particularly
sensitive future comparisons are the exact class universe used by
the local finite AP interface, the finite-orbit notion for infinite
Γ, the printed d-closure language and the treatment of constants.
