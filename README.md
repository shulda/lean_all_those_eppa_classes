# All those EPPA classes — Lean formalization

Formalization of the general constructions in

> J. Hubička, M. Konečný, J. Nešetřil, *All those EPPA classes
> (Strengthenings of the Herwig--Lascar theorem)*.

The authoritative paper source is maintained separately in the private
Overleaf mirror.  This public repository contains the Lean formalization and
its audit/status material.

For the live paper-to-Lean dependency/status map, see [FORMALIZATION.md](FORMALIZATION.md).

## Scope and priorities

The primary target is the general EPPA machinery:

1. foundational definitions for the paper's generalized structures and maps;
2. EPPA witnesses and coherent EPPA;
3. the unrestricted construction, including irreducible-structure faithfulness;
4. the restricted/tree-like construction and local control;
5. the principal general corollaries and readable regression examples.

The principal general theorems (including the restricted/tree-like EPPA
construction, the Herwig–Lascar generalisation, the locally finite
completion transfer, and Proposition 11.3) have now passed the complete
Lean build and axiom audit; see `FORMALIZATION.md` for precise scope.

The current final **small regression** is a completely readable theorem
for finite integer metrics, uniformly in D, strengthening ordinary EPPA
by preserving the maximum size of a clique of pairwise distance 1.
The all-D conclusion is not yet proved; its explicit quantifier-level
statement is in `Examples/IntegerMetricReaderFacingEPPA.lean`,
with the proof strategy in `METRIC_EPPA_ROADMAP.md`.

After the metric regression, the remaining large planned paper application
is **EPPA for k-orientations with d-closures** (Section 9.3 of
the paper; closely related to Hrushovski predimension constructions).
This is the deferred Hrushovski-related application referred to in older
project notes, not a third independently scheduled regression.
A final manuscript-statement/API audit is also planned.

## Human-readable regression examples

As the API develops, the repository will contain short theorem statements
whose mathematical meaning is easy to inspect.  Planned checkpoints include:

- finite sets have coherent EPPA;
- finite graphs have EPPA;
- finite 3-uniform hypergraphs have EPPA (testing irreducible-structure
  faithfulness);
- for every natural D, every finite metric space with distances in
  `{0,1,...,D}` has a finite metric EPPA witness **with the same distance
  alphabet AND the same maximum size of a unit-distance clique**
  (testing both irreducible-structure faithfulness and the restricted/
  tree-like machinery). The cases D=0 and D=1 are proved; the
  full-D result remains open.

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
