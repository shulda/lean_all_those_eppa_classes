# Lean verification and reproducibility

**Reference revision:**
[`d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d`](https://github.com/shulda/lean_all_those_eppa_classes/commit/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d)
(16 October 2026).

The [GitHub Actions Lean CI](https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/38938495445)
reported **success** on exactly that revision. The workflow is
[`.github/workflows/lean.yml`](../../.github/workflows/lean.yml).
It builds the Lean project and audits the axioms of the root
`AllThoseEPPA` library. It allows only:

- `propext`
- `Classical.choice`
- `Quot.sound`

The check is designed to disallow locally introduced axioms and
`sorryAx` dependencies. This report records **CI results**, rather
than claiming that the present wiki author independently reran
all of Lean/mathlib on another machine.

## Local reproduction

Use Lean and Mathlib versions pinned by
[`lean-toolchain`](../../lean-toolchain) and
[`lake-manifest.json`](../../lake-manifest.json).

```bash
git clone https://github.com/shulda/lean_all_those_eppa_classes.git
cd lean_all_those_eppa_classes
git checkout d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d
lake update
lake exe cache get
lake build
```

The exact GitHub Actions job is the authoritative record for
the axiom audit. In a local Lean file, inspect the major exported
theorems and their dependencies using `#check` and
`#print axioms` after importing `AllThoseEPPA.MainTheorems`.

An API regression example is
[`MainTheoremsPublicAPIUsage.lean`](../../AllThoseEPPA/Examples/MainTheoremsPublicAPIUsage.lean);
other public regressions cover metric and rooted k-orientation imports.

## Three different correctness questions

**Kernel integrity.** Lean has checked the proof term against
the elaborated Lean theorem and its imported axioms.

**Statement fidelity.** The types `Structure`, `Embedding`,
`HasFiniteRelabelOrbit`, `IsCoherentEPPAWitness`,
`IsIrreducibleStructureFaithful` etc. express the intended
paper notions, including all side conditions. This requires
mathematical inspection and possibly formal bridge lemmas.

**Application coverage.** A concrete model representation satisfies
the prerequisites of a general theorem, and the resulting witness
has the exact originally advertised type and class membership.
The [rooted-orientation scope gap](Adversarial-audit.md)
illustrates why this must be checked separately.

A successful build certifies the first, not the other two.
Source-to-Lean findings belong in
[Published statements](Published-statements.md) and
[Adversarial audit](Adversarial-audit.md).

## Updating the baseline

When the repository changes, record the new tested commit,
the green workflow URL, and any semantic impact on the printed
paper crosswalk. Avoid replacing this pinned historical record
by a floating “latest” claim without checking CI.
