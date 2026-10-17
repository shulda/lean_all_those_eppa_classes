# All those EPPA classes — a verified Lean research library

This wiki is a mathematical and practical guide to the Lean 4 formalization of
J. Hubička, M. Konečný and J. Nešetřil, *All those EPPA classes
(Strengthenings of the Herwig–Lascar theorem)*.

Its purpose is **twofold**: help mathematicians reuse the verified EPPA
constructions, and make it possible to audit what has *actually* been proved.
A green Lean build certifies a proof of its elaborated statement; it does not
by itself certify that the statement matches a printed mathematical theorem.

**Audit baseline:** repository main commit
[`d85fda061d0b`](https://github.com/shulda/lean_all_those_eppa_classes/commit/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d)
(16 October 2026), with the [complete successful Lean CI and axiom audit](https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/38938495445).
The source comparison below uses the public
[paper](https://arxiv.org/abs/1902.03855), not any private revised Overleaf manuscript.

## Navigation

| Page | Purpose |
| --- | --- |
| [Published statements](Published-statements.md) | Numbered theorem-to-Lean crosswalk, strengths, extra assumptions, and unexported cases |
| [Mathematical definitions](Mathematical-definitions.md) | Γ-languages, set-valued functions, partial isomorphisms, coherent EPPA, irreducibility, faithfulness, and completions |
| [Proof architecture](Proof-architecture.md) | Why the four general constructions work and where to find their Lean implementations |
| [Using the library](Using-the-library.md) | Install a pinned revision, import the public API, and apply its main theorems |
| [Applications and regression tests](Applications.md) | Hypergraphs, bounded integer metrics, and the higher-arity d-closure orientation application |
| [Adversarial audit](Adversarial-audit.md) | Explicit semantic checks, caveats, and outstanding author/source comparisons |
| [Verification](Verification.md) | Reproducible build, kernel/axiom trust, CI baseline and proof versus statement fidelity |
| [Publishing](Publishing.md) | How version-controlled pages synchronize to the actual GitHub Wiki |

## The public mathematical entry points

```lean
import AllThoseEPPA.MainTheorems

#check AllThoseEPPA.MainTheorems.unrestrictedFaithfulCoherentEPPA
#check AllThoseEPPA.MainTheorems.restrictedLocallyTreeLikeEPPA
#check AllThoseEPPA.MainTheorems.herwigLascar
#check AllThoseEPPA.MainTheorems.locallyFiniteEPPA
#check AllThoseEPPA.MainTheorems.locallyFiniteCoherentEPPA
#check AllThoseEPPA.MainTheorems.completionIffStrong
```

The first three produce finite irreducible-structure faithful witnesses,
with the precise coherence conditions described in
[Published statements](Published-statements.md). The local-finiteness
theorems transfer EPPA between classes; they do not manufacture a local
completion hypothesis. Proposition 11.3 upgrades a completion to an
injective one; it does not assert an automorphism lift.

The primary [public API guide](../../MAIN_THEOREMS_API.md) and the
[formalization status ledger](../../FORMALIZATION.md) remain available.

## Correct interpretation of the published k-orientation class

**The rootedness condition in Lean matches the paper.** In the public
paper (Section 12.5), Definition 12.10 sets
`D_d^k = { d(G) : s(G) ∈ D_{s+}^k }`, where the preceding definition
of `D_{s+}^k` requires **every vertex to have a reachable root**.
Thus `HasReachableRoots k` in
`KOrientationsEPPA.rootedFaithfulCoherent` is not an additional
restriction on the class covered by the published result,
**Theorem 12.12**. Theorem 12.9 was mistakenly cited in an earlier
wiki draft; it is actually Definition 12.9.

The paper explicitly excludes rootless components from its
`d`-closure class, noting that they would require constants.
A general theorem for `d`-closures allowing such components
is a *different* target, not a missing case of Theorem 12.12.
See the [source-to-Lean crosswalk](Published-statements.md) and
[correction record](Adversarial-audit.md).

## Sources and changes

The authoritative source for this wiki is [`docs/wiki/`](./README.md)
in the main repository. It is published to the separate
[GitHub Wiki](https://github.com/shulda/lean_all_those_eppa_classes/wiki)
by a GitHub Actions workflow once the Wiki repository has been initialized.
Statements of mathematical scope should be updated together with code
changes, not only in the web Wiki editor.

Primary reference: J. Hubička, M. Konečný, J. Nešetřil,
*All those EPPA classes (Strengthenings of the Herwig–Lascar theorem)*,
[arXiv:1902.03855](https://arxiv.org/abs/1902.03855).
