# All those EPPA classes — Lean formalization

Formalization of the general constructions in

> J. Hubička, M. Konečný, J. Nešetřil, *All those EPPA classes
> (Strengthenings of the Herwig--Lascar theorem)*.

The authoritative paper source is maintained separately in the private
Overleaf mirror.  This public repository contains the Lean formalization and
its audit/status material.

## Scope and priorities

The primary target is the general EPPA machinery:

1. foundational definitions for the paper's generalized structures and maps;
2. EPPA witnesses and coherent EPPA;
3. the unrestricted construction, including irreducible-structure faithfulness;
4. the restricted/tree-like construction and local control;
5. the principal general corollaries and readable regression examples.

The later application to Hrushovski constructions is deliberately deferred
until the general construction is formalized and the API is satisfactory.

## Human-readable regression examples

As the API develops, the repository will contain short theorem statements
whose mathematical meaning is easy to inspect.  Planned checkpoints include:

- finite sets have coherent EPPA;
- finite graphs have EPPA;
- finite 3-uniform hypergraphs have EPPA (testing irreducible-structure
  faithfulness);
- finite metric spaces with distances in `{0,1,...,D}` have EPPA, preferably
  uniformly in the natural number `D` (testing the restricted/tree-like
  machinery).

These are not merely examples: they are intended as regression tests for the
mathematical API.

## Trust policy

GitHub Actions builds the complete Lean library on every push and pull request.
CI also runs an axiom audit.  Project declarations are not allowed to depend
on `sorryAx` or custom axioms; only Lean/mathlib's standard logical axioms
(`propext`, `Classical.choice`, and `Quot.sound`) are allowed.

Mathematically substantive corrections discovered during formalization are
made transparently in the paper source as separate commits, together with an
inline formalization note explaining what changed.

## Lean version

The project tracks the stable Lean/mathlib release pinned in
`lean-toolchain`, `lakefile.toml`, and (once generated) `lake-manifest.json`.
