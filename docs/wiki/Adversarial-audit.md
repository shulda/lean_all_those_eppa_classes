# Adversarial mathematical audit

**Baseline:** [commit `d85fda061d0b`](https://github.com/shulda/lean_all_those_eppa_classes/commit/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d);
[green full Lean build + axiom check](https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/38938495445)
(16 October 2026).
**Comparison source:** the [public paper](https://arxiv.org/abs/1902.03855).
This is an initial source/definition audit, **not** an external
referee certificate and not a claim that every application has
been formalized.

## Audit dimensions

1. **Lean trust:** is the theorem kernel-checked with only accepted
   axioms, and does its import dependency actually reach the proof?
2. **Logical content:** what do the definitions and elaborated
   hypotheses/conclusions mean, including all closure, Γ-action,
   finiteness and coherent-selection quantifiers?
3. **Source correspondence:** does the checked type imply the
   *exact printed theorem*? Is its input class unexpectedly
   narrower or an output clause absent?
4. **Reusability:** can a downstream formalization invoke a
   stable named theorem without implicitly assuming the
   result it was meant to prove?

The library CI addresses (1). The findings below principally
address (2)–(4); they should be maintained with code changes.

## Concrete findings

| Priority | Finding | Classification | Action |
| --- | --- | --- | --- |
| **Resolved 2026-10-17** | Earlier wiki draft alleged an extra reachable-root hypothesis for published k-orientations Theorem 12.9 | **False finding.** The actual result is **Theorem 12.12**; its input class `D_d^k` is defined in Definition 12.10 using `D_{s+}^k`, hence it already requires reachable roots | Correct crosswalk and retain this source-reading correction for traceability |
| **Resolved 2026-10-17** | Earlier draft alleged that Theorem 1.6 required only AP and that Lean added SAP | **False finding.** Published Theorem 1.6 explicitly assumes **strong amalgamation (SAP)**; the Lean facade matches. The separate AP-level Lean theorem is a genuine strengthening | Correct crosswalk, avoid presenting extra generality as a missing paper clause |
| **P1** | Metric regression gives **ordinary** EPPA in bounded integer metrics, not the printed coherent metric application | A strong regression but **not an exact published-statement endpoint** | Export coherent metric source-facing theorem if desired; do not retroactively label ordinary EPPA coherent |
| **P2** | Theorem 1.2 Lean version omits printed irreducibility of A and allows n=0 | **Safe strengthening** | Document the extra generality rather than weaken code |
| **P2** | Herwig–Lascar ambient N in Lean has arbitrary carrier cardinality; printed text discusses finite/countable | **Safe strengthening** | Retain explicit finite orbit and exact forbidden notion |
| **P2** | Older development notes and comments can describe completed tasks as “open”; project log has historical checkpoints | Documentation drift | Treat Lean declaration and CI as authority; separate historical notes from current status |
| **P2** | Printed assertions with constants, Theorem 1.3/Corollary 1.4, and other separate applications lack a verified stand-alone crosswalk entry here | **Not independently matched** | Audit by exact statement and declaration, not by inference from a generic result |

## Correction of an initial theorem-versus-definition misreading

The initial wiki draft treated
`KOrientationsEPPA.rootedFaithfulCoherent` as narrower than
the published orientation theorem and cited “Theorem 12.9”.
This was **incorrect**.

The public [arXiv:1902.03855v4, printed pp. 51–52](https://arxiv.org/pdf/1902.03855)
first introduces `D_{s+}^k` as the class of
k-orientations in which every vertex has a reachable root.
**Definition 12.10** then defines
`D_d^k = {d(G) : s(G) ∈ D_{s+}^k}`.
**Theorem 12.12** gives coherent faithful EPPA for
exactly this class. In the paper, “12.9” is **Definition
12.9** of the unary successor expansion `s(G)`.

The rootedness assumption in the Lean theorem is therefore
the explicit class-membership condition in the paper, not
a restriction introduced by formalization. The root-fibre
functions are present at all positive arities in Lean.

The oriented 3-cycle at k=1 illustrates only that
`D^1` (all finite 1-orientations) is larger than
`D_d^1`. It is **not** a counterexample to the match
between Lean and the published theorem. The paper excludes
rootless vertices because they would require constants,
as explicitly discussed after Definition 12.10.

The same review corrected the purported AP/SAP mismatch:
published **Theorem 1.6 explicitly assumes SAP**;
our public Lean facade faithfully reflects it, while a
separately proved AP-level version is stronger.

## Audited foundational definitions

The following have been read directly from Lean source:

- `Language` and `Action`: arity-indexed symbols, non-nullary
  relations, arbitrary positive relational arity, unary
  set-valued functions, Γ acting on symbols.
- `Homomorphism` and `Embedding`: Γ-component, relation
  forward preservation versus reflection, inclusion versus
  equality for function-value images.
- `PartialIsomorphism.Equivalent`, `CoherentTriple` and
  `CoherentExtension`: domain-aware equality, matching
  target/source, ordered composition, invariant selected
  total automorphisms.
- `FreeDecomposition` and `IsIrreducibleStructureFaithful`:
  function-closed free amalgams and movement of each
  irreducible substructure into the distinguished source copy.
- `FiniteForbiddenFamily.Avoids`: no Γ-homomorphism-embedding,
  not just absence of an induced configuration.
- `HasLocallyFiniteAutomorphismPreservingCompletion`:
  a *uniform finite bound per pair A,B₀* and a global
  strong completion with a coherent group-compatible
  automorphism lift.

The definitions and exact code locations are recorded
in [Mathematical definitions](Mathematical-definitions.md).
This review is a *semantic inspection*, not a machine-checked
equivalence to a formalization of the printed prose.

## Further proof obligations before an “exact paper” certificate

The following remain research/audit tasks, not admissions in
the already verified Lean theorems:

- Independently compare the entire **current authoritative
  manuscript**, not only the public version, against the
  version-pinned Lean types and theorem numbers.
- Compare the remaining technical definitions and numbered
  intermediate claims of Section 12.5, while keeping the
  already resolved rootedness interpretation fixed.
- Audit the paper's remaining individually numbered
  corollaries and applications, and add explicit public
  statements where the derivation is routine.
- For substantive interfaces, construct adversarial toy
  encodings: nontrivial Γ symbol action, partially undefined
  unary set-valued functions, nonempty closed substructures,
  homomorphism-embedding versus genuine embedding,
  and noninjective completion versus automorphism-preserving lift.
- Keep a version-pinned record of any newly found discrepancy
  and either repair the Lean theorem, add a bridge, or
  explicitly mark the published claim as not yet covered.

## What is *not* a finding

Nothing here shows an unsound Lean proof, a hidden axiom,
or a logical contradiction. **The alleged k-orientation
scope gap and AP/SAP discrepancy were both source-reading
errors**, now corrected. The metric coherent-versus-ordinary
distinction remains a genuine difference between a
regression theorem and the separately printed application.
