# All those EPPA classes — Lean formalization


## Research wiki and semantic audit

The [research wiki](https://github.com/shulda/lean_all_those_eppa_classes/wiki)
([version-controlled source](docs/wiki/README.md)) explains the mathematical
constructions, gives practical reuse instructions, and audits the correspondence
between the paper and the exact Lean declarations.
See especially the [published-statement crosswalk](docs/wiki/Published-statements.md)
and [adversarial scope audit](docs/wiki/Adversarial-audit.md).
A green Lean proof/axiom audit certifies the *formalized* theorem, not automatically
the exact printed statement of every application.


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

## Reusing the *main theorems* in other Lean projects

**Primary public import:**

```lean
import AllThoseEPPA.MainTheorems
```

This is the intended entry point for new EPPA formalizations.
It exposes the unrestricted coherent faithful EPPA construction,
the restricted/tree-like theorem, the finite-forbidden-family
Herwig–Lascar theorem, the ordinary and coherent locally finite
subclass transfer, and Proposition 11.3.

Start with the **[main theorems public API guide](MAIN_THEOREMS_API.md)**.
It contains a theorem-to-Lean map, exact assumptions (Γ-symbol actions,
finite relabel orbit, set-valued unary functions, forbidden families,
SAP and local completion), dependency installation, and checked
application patterns.
The [consumer smoke test](AllThoseEPPA/Examples/MainTheoremsPublicAPIUsage.lean)
uses only this facade and runs in CI.

The metric and hypergraph results discussed next are **regression
examples**, not the primary reusable construction API.

The **final small regression is now Lean-checked**: for every natural D,
every finite metric A with integer distances in {0,...,D} admits a finite
D-bounded metric EPPA witness B with **exactly the same maximum size of a
pairwise distance-one clique**. The standalone mathematical quantifiers
are in `AllThoseEPPA/Examples/IntegerMetricReaderFacingEPPA.lean`; the
unconditional proof is
`IntegerMetric.Bridge.allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique`
in `AllThoseEPPA/Examples/IntegerMetricAllDMainTheorem.lean`
(full Lean build + axiom audit on PR #235; merged through PR #237).
This proof genuinely invokes the already-verified unrestricted faithful
and restricted/tree-like EPPA constructions, rather than an external metric
EPPA theorem. See `METRIC_EPPA_ROADMAP.md` for the dependency and audit map.

**The remaining large paper application has now also been Lean-checked:**
finite rooted k-orientations with the genuine higher-arity d-closures
(Section 9.3, manuscript `thm:DF`). Every finite rooted
outdegree-≤k orientation has a finite rooted witness with coherent
EPPA and irreducible-structure faithfulness for its ORIGINAL
full d(A), not merely the unary successor reduct.
The verified result is
[`Applications.KOrientations.exists_rootedKOrientation_faithfulCoherentDEPPa`](AllThoseEPPA/Applications/KOrientations/RootedKOrientationDFinalEPPA.lean)
now integrated on `main` through [PR #242](https://github.com/shulda/lean_all_those_eppa_classes/pull/242),
with [full main CI](https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/38938495445)
and its [original application verification](https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/38926049553).
**Scope caveat:** the Lean theorem assumes every input vertex can reach a root
(`HasReachableRoots k`). This is not automatic for all finite k-orientations;
the public paper's Theorem 12.9 is broader. The discrepancy is tracked in
the [wiki audit](docs/wiki/Adversarial-audit.md).

**Supported external import:** `import AllThoseEPPA.KOrientationsEPPA`.
See [the exact assumptions, theorem statement and consumer
smoke test](K_ORIENTATIONS_EPPA_API.md). The result does not
assert EPPA for arbitrary unrooted orientations or unoriented reducts.

## Using the metric regression in another Lean project

The supported external import is:

```lean
import AllThoseEPPA.IntegerMetricEPPA
```

The public theorems are
`AllThoseEPPA.IntegerMetric.eppaPreservingUnitCliqueNumber D A`
and `AllThoseEPPA.IntegerMetric.eppa D A`.
They return explicit existential witnesses for an input
`A : BoundedNatMetric D α`, `[Finite α]`.

**[External-project installation, complete API, and compiled usage example](INTEGER_METRIC_EPPA_API.md)**.
The consumer smoke test is
[`AllThoseEPPA/Examples/IntegerMetricPublicAPIUsage.lean`](AllThoseEPPA/Examples/IntegerMetricPublicAPIUsage.lean).

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
  tree-like machinery). This strengthened, uniform all-D assertion
  is now fully Lean-checked and integrated (PRs #235–#237).

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
