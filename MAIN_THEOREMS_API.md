# Reusing the main theorems of *All those EPPA classes*

**This is the primary external-project API of this repository.**
Metric and hypergraph EPPA theorems are examples/regression tests,
not the recommended abstraction for new EPPA projects.

## Import and installation

Add the formalization as a dependency in your consuming project's
`lakefile.toml`:

```toml
[[require]]
name = "AllThoseEPPA"
git = "https://github.com/shulda/lean_all_those_eppa_classes.git"
rev = "<verified-main-theorems-commit>"
```

Replace the placeholder with the full Git commit SHA of the checked
public-API release you intend to use. Pinning is preferred over
tracking `main`, because this is a research library, not yet a
semantically versioned API. The repository currently pins Lean
`v4.34.1` and Mathlib `v4.34.1`; resolve any conflicting
Mathlib dependency in your consumer. Then run `lake update` and
`lake build` (and `lake exe cache get` where applicable).

In Lean:

```lean
import AllThoseEPPA.MainTheorems
open AllThoseEPPA
```

This imports the four principal formalized results, their necessary
vocabulary and Proposition 11.3. You do **not** need to import
`AllThoseEPPA` (the entire umbrella file), any internal valuation
or sparsening proofs, or the separate integer-metric API.

## Result index (Lean declaration names are authoritative)

| Mathematical content / manuscript label | Public entry point | Input | Important output |
| --- | --- | --- | --- |
| Unrestricted faithful coherent EPPA, `thm:nreppa` | `MainTheorems.unrestrictedFaithfulCoherentEPPA` | Finite A, finite Γ-relabel orbit | Finite B, exact Γ-embedding, coherent EPPA, irreducible-structure faithfulness |
| Restricted/tree-like EPPA, `thm:maintree` | `MainTheorems.restrictedLocallyTreeLikeEPPA` | Finite A and finite EPPA witness B₀ with embedding ψ, bound n | Finite faithful B, EPPA, homomorphism-embedding B→B₀, each n-small closed substructure maps into a tree of full A-copies; conditional coherence |
| Herwig–Lascar generalization, `thm:main` | `MainTheorems.herwigLascar` | Finite forbidden family F, finite-orbit A, possibly infinite N∈Forb(F), embedding A→N extending partial automorphisms | Finite coherent faithful EPPA witness B∈Forb(F) |
| Locally finite subclass transfer, `thm:mainstrong` / Theorem 1.6 | `MainTheorems.locallyFiniteEPPA`; `MainTheorems.locallyFiniteCoherentEPPA` | Hereditary finite Γ-strong-AP class K of irreducibles, ambient EPPA class E, K⊆E, automorphism-preserving local finiteness | Ordinary/coherent EPPA in K, respectively |
| Completion upgrade, Proposition 11.3 | `MainTheorems.completionIffStrong` | Finite source A; hereditary finite strong-AP class K | Ordinary completion exists iff globally injective completion exists |

The source filenames and paper-reference labels are tracked in
[`FORMALIZATION.md`](FORMALIZATION.md). In particular, follow those
labels rather than assuming that the printed theorem numbering is
identical across every manuscript version.

## Common mathematical vocabulary

The API lives under `AllThoseEPPA`:

- `Language` carries arity-indexed relation symbols and
  set-valued function symbols, with `[L.HasUnaryFunctions]` requiring
  that every function symbol has arity one. Relations may have
  arbitrarily large **positive** arity. Ordinary finite-valued
  (single-valued) unary functions can be represented by singleton
  sets if the formalization of the application supplies the
  appropriate encoding.
- `Structure L α` is a structure on carrier type α. `[Finite α]`
  is the usual typeclass hypothesis; only finite carriers are
  required for the input witnesses. The facade's unrestricted theorem
  now also accepts `[Finite α]` instead of requiring a chosen
  `[Fintype α]`.
- `act : L.Action Γ` describes a group Γ acting on the relation
  and function symbols, respecting arities. Theorems cover
  **nontrivial** symbol permutations. Use
  `Language.Action.trivial L Γ` for trivial actions, supplying
  a `Group Γ` instance.
- `Structure.Embedding act A B` is an **exact** Γ-embedding.
  `Structure.IsEPPAWitness act ι` means every partial
  automorphism of A extends **along ι**. Its equation includes
  both the vertex action and the Γ-language component.
- `Structure.IsCoherentEPPAWitness act ι` is
  `Nonempty (Structure.CoherentExtension act ι)`.
  Once destructured as `⟨c⟩`, an individual extension is
  `c.extension p`. The coherence law uses the project's
  `PartialIsomorphism.CoherentTriple`.
- `Structure.IsIrreducibleStructureFaithful act ι` is the
  manuscript's *irreducible-structure faithfulness*, stronger
  than merely `B.IsIrreducible`. It is a predicate on the
  particular distinguished embedding.

These predicates are fully specified in the imported modules
(`Language.lean`, `Structure.lean`, `Map.lean`,
`EPPA.lean`, and `Faithful*.lean`).

## Example A: unrestricted faithful coherent EPPA

```lean
import AllThoseEPPA.MainTheorems

open AllThoseEPPA

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

example {α : Type v} [Finite α]
    (act : L.Action Γ) (A : Structure L α)
    (hOrbit : A.HasFiniteRelabelOrbit act) :
    ∃ (β : Type (max u v)) (_ : Finite β)
      (B : Structure L β) (ι : Structure.Embedding act A B),
      Structure.IsEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι := by
  obtain ⟨β, hβ, B, ι, ⟨c⟩, hFaith⟩ :=
    MainTheorems.unrestrictedFaithfulCoherentEPPA act A hOrbit
  exact ⟨β, hβ, B, ι, c.isEPPAWitness act, hFaith⟩
```

Here `hOrbit` is not implied merely by finiteness of A if Γ
acts with an infinite relabelling orbit. In the familiar finite
language/trivial-action cases it is often easy to establish;
it is not silently supplied by this library.

The checked consumer file additionally demonstrates extracting
conditional coherence from the restricted theorem, and using
Herwig–Lascar and the local-finiteness transfer:
[`AllThoseEPPA/Examples/MainTheoremsPublicAPIUsage.lean`](AllThoseEPPA/Examples/MainTheoremsPublicAPIUsage.lean).

## Example B: restricted / locally tree-like EPPA

Assume `[Finite α]`, `[Finite β]`,
`A : Structure L α`, `B₀ : Structure L β`,
`ψ : Structure.Embedding act A B₀` and
`hEPPA : Structure.IsEPPAWitness act ψ`.
Then for any `n : ℕ`:

```lean
obtain ⟨δ, hδ, B, ι, hEPPAnew, hFaith, hProjection,
        hSmallTrees, hCoherentTransfer⟩ :=
  MainTheorems.restrictedLocallyTreeLikeEPPA
    act A B₀ ψ hEPPA n
```

This is an existence theorem and does **not** choose a canonical
witness for computations. `hSmallTrees` quantifies over every
`S : Set δ` that is closed under the unary functions and has
`S.ncard ≤ n`. It returns a `TreeLike.TreeAmalgamation` of full
A-copies and a homomorphism-embedding of the induced S-structure.
The projection B→B₀ is a homomorphism-embedding, not generally an
injective induced embedding. If the original `ψ` has coherent
EPPA, apply `hCoherentTransfer` to obtain coherent EPPA for ι.

## Example C: Herwig–Lascar / forbidden configurations

Build
`F : HerwigLascar.FiniteForbiddenFamily L` with a finite
code set and a possibly different finite carrier type for
each forbidden structure. Supply
`hN : F.Avoids act N` for an ambient structure N, and a
genuine Γ-embedding `a : Structure.Embedding act A N` with
`hExt : Structure.IsEPPAWitness act a`.
N **need not be finite**. Then:

```lean
obtain ⟨δ, hδ, B, ι, hCoherent, hFaithful, hAvoids⟩ :=
  MainTheorems.herwigLascar F act A hOrbit N a hExt hN
```

Here `F.Avoids act B` forbids
**Γ-homomorphism-embeddings**, *not* ordinary homomorphisms,
only induced copies, or induced-subgraph embeddings.
Converting a preferred application-specific definition of
`Forb(F)` to this one is an explicit proof obligation.

## Example D: locally finite subclass theorem

The paper-facing route uses

```lean
K : TreeLike.HereditaryFiniteStrongAmalgamationClass act
E : {V : Type (max u v)} → Structure L V → Prop
```

and requires `K.toAmalgamationClass.mem A → E A`,
ordinary (or coherent) finite-class EPPA for E,
irreducibility of every finite member of K, and
`TreeLike.HasLocallyFiniteAutomorphismPreservingCompletion
act A B₀ K.toAmalgamationClass` for every relevant finite
A∈K and B₀∈E.

Then:

```lean
have hKEPPA : K.toAmalgamationClass.HasEPPA :=
  MainTheorems.locallyFiniteEPPA
    act K E hSub hE hIrr hLocallyFinite
```

and the coherent version is `locallyFiniteCoherentEPPA`
with `hE : TreeLike.FiniteClassHasCoherentEPPA act E`.
A concrete A∈K can be passed to `hKEPPA A hA` to obtain
an existential witness and `K.mem B`.

The local-finiteness predicate is **not** merely the statement
that each small piece can be completed. It quantifies a
bound `n` depending on the input (A,B₀), and concludes an
automorphism-preserving **strong** completion of B whenever
the stipulated small completions, irreducible-source condition
and projection into B₀ hold. The lift must preserve identity,
composition, and Γ-language components.

There is also a verified theorem with the *weaker* plain
amalgamation-class interface, without heredity/SAP:
`TreeLike.locallyFiniteSubclass_hasEPPA` (and its coherent
variant) in `StrongCompletionManuscriptSubclass.lean`.
The public facade above deliberately exposes the more
familiar, literal manuscript hereditary SAP version first.

## Proposition 11.3 and precise scope

`MainTheorems.completionIffStrong act K A` is the proved
equivalence between `HasCompletion A` (a Γ-homomorphism-
embedding, possibly noninjective) and `HasStrongCompletion A`
(additionally injective). **Neither conclusion automatically
provides an automorphism-preserving lift.** This distinction is
essential for the locally finite theorem.

All exported statements are proven in the repository's
audited Lean formalization; they are not axioms. They give
existence of finite witnesses, **not** an executable program,
numerical bounds on witness size, or unconditional EPPA for
arbitrary hereditary classes. Coherent and faithfulness
properties are asserted only when the specific theorem
provides them.

For the full paper-to-formalization dependency map see
[`FORMALIZATION.md`](FORMALIZATION.md). Source endpoints:
[`UnrestrictedFaithfulEPPA.lean`](AllThoseEPPA/UnrestrictedFaithfulEPPA.lean),
[`TreeLikeUnrestrictedMaintree.lean`](AllThoseEPPA/TreeLikeUnrestrictedMaintree.lean),
[`HerwigLascarTheorem.lean`](AllThoseEPPA/HerwigLascarTheorem.lean),
[`StrongCompletionHereditaryStrongAmalgamation.lean`](AllThoseEPPA/StrongCompletionHereditaryStrongAmalgamation.lean).

The root library build and CI axiom audit (permitting only
`propext`, `Classical.choice`, `Quot.sound` under
`AllThoseEPPA`) protect the smoke test and these public
entry points. When updating the dependency, keep the consumer
pinned to a known green SHA and recompile.
