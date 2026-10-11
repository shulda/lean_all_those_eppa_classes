# Reusing bounded integer metric EPPA from another Lean project

**Public module:** `AllThoseEPPA.IntegerMetricEPPA`

**Lean version pinned in this repository:** `leanprover/lean4:v4.34.1`
(with Mathlib `v4.34.1`). The API is now tracked by an import-only
consumer smoke test inside the repository.

## 1. Add the library as a Lake dependency

In the *consumer* project's `lakefile.toml`, add:

```toml
[[require]]
name = "AllThoseEPPA"
git = "https://github.com/shulda/lean_all_those_eppa_classes.git"
rev = "<tested-commit-sha>"
```

Replace the placeholder with the full commit SHA of a tested version
containing this API. **Pin a commit**, rather than following moving
`main`; no independent API-versioned release is promised yet.
Use a compatible `lean-toolchain` (currently
`leanprover/lean4:v4.34.1`) and run:

```sh
lake update
lake exe cache get
lake build
```

Mathlib is a transitive dependency of `AllThoseEPPA`; avoid adding a
different Mathlib version in the consuming project. A project that
already has its own Mathlib dependency must reconcile its version
with the one locked by this library.

Then, in any Lean file:

```lean
import AllThoseEPPA.IntegerMetricEPPA

open AllThoseEPPA.IntegerMetric
```

You do **not** need to import the underlying paper machinery or the
large `AllThoseEPPA` umbrella module.

## 2. What you get

The metric vocabulary is
`AllThoseEPPA.IntegerMetric.BoundedNatMetric D α`. Its `dist`
function takes values in `ℕ`; it satisfies the usual metric axioms
(in particular, distance zero implies equality), with
`dist x y ≤ D`. Thus the metric is genuinely finite-valued in
`{0, ..., D}`, rather than a pseudometric or a graph path length.

The two recommended theorems are:

- `IntegerMetric.eppaPreservingUnitCliqueNumber D A` — **preferred**:
  finite witness, isometric embedding, extension of every partial
  isometry, and equality of largest distance-one clique cardinalities.
- `IntegerMetric.eppa D A` — same without the clique conclusion.

Here `D : ℕ`, `α : Type u`, `[Finite α]`, and
`A : BoundedNatMetric D α`. A `[Fintype α]` instance already
implies `[Finite α]`. There is no restriction to `D ≥ 2`.
Empty spaces and `D = 0,1` are included.

**Partial isometry:** the input is an equivalence
`p : U ≃ V` of subtype sets `U V : Set α`. If distances agree on
`U`, the output contains a permutation `g : Equiv.Perm β` that
is an isometry of all of `B` and satisfies
`g (ι x.1) = ι (p x).1` for every `x : U`.

The clique number is
`IntegerMetric.maximumUnitCliqueSize B`; its value is zero on an
empty metric space. The assertion is **equality**, not just an upper
bound. Note that ordinary metric EPPA alone does not imply this
extra preservation property for a given witness.

## 3. Working consumer pattern (also checked in CI)

```lean
import AllThoseEPPA.IntegerMetricEPPA

open AllThoseEPPA.IntegerMetric

universe u

example (D : ℕ) {α : Type u} [Finite α]
    (A : BoundedNatMetric D α)
    (U V : Set α) (p : U ≃ V)
    (hp : ∀ x y : U,
      A.dist x.1 y.1 = A.dist (p x).1 (p y).1) :
    ∃ (β : Type u) (_ : Finite β)
      (B : BoundedNatMetric D β) (ι : α ↪ β)
      (g : Equiv.Perm β),
      (∀ x y : α, B.dist (ι x) (ι y) = A.dist x y) ∧
      (∀ x y : β, B.dist (g x) (g y) = B.dist x y) ∧
      (∀ x : U, g (ι x.1) = ι (p x).1) ∧
      maximumUnitCliqueSize B = maximumUnitCliqueSize A := by
  obtain ⟨β, hβ, B, ι, hIsometric, hExtend, hClique⟩ :=
    eppaPreservingUnitCliqueNumber D A
  obtain ⟨g, hgIsometry, hgExtends⟩ := hExtend U V p hp
  exact ⟨β, hβ, B, ι, g,
    hIsometric, hgIsometry, hgExtends, hClique⟩
```

The in-repository Lean-checked source is
[`AllThoseEPPA/Examples/IntegerMetricPublicAPIUsage.lean`](AllThoseEPPA/Examples/IntegerMetricPublicAPIUsage.lean).
This is intentionally a separate module importing **only**
`AllThoseEPPA.IntegerMetricEPPA`: it catches accidental changes to
the entry point and demonstrates how to eliminate the existential.

## 4. Scope and interoperability

- **No extra order, Γ-action, chosen partial maps, coherent extension,
  or fixed witness size is assumed.** The theorem is an existential
  ordinary-EPPA statement, not a computable witness-generation
  algorithm or a quantitative size bound.
- `BoundedNatMetric` is a small, **project-specific structure**;
  it is not automatically identified with Mathlib's
  `[MetricSpace α]` (whose `dist` is real-valued). A consumer
  whose starting point is a real-valued Mathlib metric must supply a
  compatible bounded natural-valued distance structure before
  invoking the theorem.
- To interpret a `BoundedNatMetric` as a real Mathlib metric,
  the formalization provides
  `A.toNatMetric.toRealMetricSpace` in
  [`IntegerMetricAsReal.lean`](AllThoseEPPA/Examples/IntegerMetricAsReal.lean).
  This conversion is used internally in the metric amalgamation
  proof; it is not an assumption of the public theorem.
- The unabridged proposition is in
  [`IntegerMetricReaderFacingEPPA.lean`](AllThoseEPPA/Examples/IntegerMetricReaderFacingEPPA.lean).
  The checked all-D proof is in
  [`IntegerMetricAllDMainTheorem.lean`](AllThoseEPPA/Examples/IntegerMetricAllDMainTheorem.lean).
  For proof dependencies and CI audit pointers see
  [`METRIC_EPPA_ROADMAP.md`](METRIC_EPPA_ROADMAP.md).

This repository uses a full Lean build and an axiom audit allowing
only `propext`, `Classical.choice` and `Quot.sound` under
`AllThoseEPPA`. The facade is a thin consequence of the verified
general EPPA proof, not a new assumption. For changes to the API,
review the consumer smoke test and require green CI before updating
a pinned dependency.
