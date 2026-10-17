# Using the AllThoseEPPA Lean library

## Install at a verified revision

In a downstream Lake project, add the dependency to
`lakefile.toml`:

```toml
[[require]]
name = "AllThoseEPPA"
git = "https://github.com/shulda/lean_all_those_eppa_classes.git"
rev = "d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d"
```

This exact commit passed the
[complete Lean and axiom CI](https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/38938495445).
The library pins Lean/mathlib v4.34.1 at this revision; use a
compatible dependency graph. Run:

```bash
lake update
lake exe cache get
lake build
```

Pinning a SHA matters: a newer `main` may reorganize internal
definitions and APIs. Read the [main theorem API document](../../MAIN_THEOREMS_API.md)
before introducing a separate downstream encoding.

## Public imports

```lean
import AllThoseEPPA.MainTheorems

#check AllThoseEPPA.MainTheorems.unrestrictedFaithfulCoherentEPPA
#check AllThoseEPPA.MainTheorems.restrictedLocallyTreeLikeEPPA
#check AllThoseEPPA.MainTheorems.herwigLascar
#check AllThoseEPPA.MainTheorems.locallyFiniteEPPA
#check AllThoseEPPA.MainTheorems.locallyFiniteCoherentEPPA
#check AllThoseEPPA.MainTheorems.completionIffStrong
```

The corresponding
[checked consumer smoke test](../../AllThoseEPPA/Examples/MainTheoremsPublicAPIUsage.lean)
shows the exact theorem application patterns. Prefer it to
inventing an implicit EPPA definition that may drop the
Γ-language component or closure requirements.

For separate regressions and applications, use:

```lean
import AllThoseEPPA.IntegerMetricEPPA
#check AllThoseEPPA.IntegerMetric.eppaPreservingUnitCliqueNumber
#check AllThoseEPPA.IntegerMetric.eppa
```

```lean
import AllThoseEPPA.KOrientationsEPPA
#check AllThoseEPPA.KOrientationsEPPA.rootedFaithfulCoherent
#check AllThoseEPPA.KOrientationsEPPA.rootedFaithfulOrdinary
```

These application statements are **not** replacements for
the general EPPA API. The k-orientation theorems require reachable
roots, exactly as does the paper's `D_d^k` class in
Definition 12.10 (published Theorem 12.12).
The integer metric result preserves the maximum
distance-one clique and uses a fixed finite distance bound.

## How to select the appropriate theorem

**Unrestricted:** given finite A with finite Γ-relabel orbit,
`unrestrictedFaithfulCoherentEPPA` gives a finite Γ-embedding
A → B with coherent EPPA and irreducible-structure faithfulness.
A finite carrier does *not* automatically imply finite relabelling
orbit under an arbitrary infinite symbol-action group.

**Restricted:** if you already have a finite EPPA witness
`ψ : A ↪ B₀`, choose any n and use
`restrictedLocallyTreeLikeEPPA`. You obtain a new finite
faithful witness with projection B → B₀ and tree-like
control of all closed n-small substructures. Coherence
transfers if the original ψ was coherent; it is **not**
automatically asserted when only ordinary EPPA is given.

**Herwig–Lascar:** supply a finite family F of finite
forbidden structures, a possibly infinite
`N ∈ Forb(F)` and an exact Γ-embedding A → N extending
all partial automorphisms of A. The output finite B lies
in `Forb(F)` and is coherent and faithful.
The forbidden maps are homomorphism-embeddings.

**Locally finite:** the class transfer requires a genuinely
automorphism-preserving strong-completion local condition.
The convenient facade uses hereditary SAP; if only AP
is available, import
`AllThoseEPPA.StrongCompletionManuscriptSubclass` and use
`TreeLike.locallyFiniteSubclass_hasEPPA` (or its coherent version).
For the precise predicates see
[Mathematical definitions](Mathematical-definitions.md).

**Completion upgrade:** `completionIffStrong` upgrades the
existence of a noninjective completion to an injective one
in the stated hereditary SAP context. It does not prove an
automorphism-preserving completion.

## Porting another combinatorial class

An application should prove its language/structure encoding,
that its partial isomorphisms represent the intended mathematical
partial maps, that `Forb(F)` really captures the desired
forbidden class, and that the output induced on the distinguished
embedding is the intended structure. For coherent EPPA also
audit the composition law; for functions audit closedness.
Make these checks *in Lean* as downstream bridge lemmas.

See the more detailed
[main API](../../MAIN_THEOREMS_API.md),
[metric API](../../INTEGER_METRIC_EPPA_API.md), and
[k-orientation API](../../K_ORIENTATIONS_EPPA_API.md).
