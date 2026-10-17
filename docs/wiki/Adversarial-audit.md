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
| **P0** | Public k-orientation theorem requires `HasReachableRoots k`; published Theorem 12.9 asserts EPPA for *all* finite k-orientations | **Mathematical scope gap**, not a kernel failure | Prove unrooted case via a Lean-checked reduction or extension, or correct the source-facing claim after comparing latest manuscript |
| **P1** | Public Theorem 1.6 facade asks hereditary **SAP** while published theorem requires **AP** | Public API is narrower, but **AP-level statement is proved** in `StrongCompletionManuscriptSubclass.lean` | Expose/document the AP-level endpoint prominently; optionally add an AP version of the public facade |
| **P1** | Metric regression gives **ordinary** EPPA in bounded integer metrics, not the printed coherent metric application | A strong regression but **not an exact published-statement endpoint** | Export coherent metric source-facing theorem if desired; do not retroactively label ordinary EPPA coherent |
| **P2** | Theorem 1.2 Lean version omits printed irreducibility of A and allows n=0 | **Safe strengthening** | Document the extra generality rather than weaken code |
| **P2** | Herwig–Lascar ambient N in Lean has arbitrary carrier cardinality; printed text discusses finite/countable | **Safe strengthening** | Retain explicit finite orbit and exact forbidden notion |
| **P2** | Older development notes and comments can describe completed tasks as “open”; project log has historical checkpoints | Documentation drift | Treat Lean declaration and CI as authority; separate historical notes from current status |
| **P2** | Printed assertions with constants, unrooted orientation variants, Theorem 1.3/Corollary 1.4 lack a verified stand-alone crosswalk entry here | **Not independently matched** | Audit by exact statement and declaration, not by inference from a generic result |

## Reproducible counterexample for the rootedness issue

Take k=1 and the directed cycle `0 → 1 → 2 → 0`.
Every vertex has exactly one outgoing edge. Thus it is a
finite 1-orientation under the standard outdegree bound.
In `Graph.lean`, a root is a vertex of outdegree **strictly less**
than one; this graph has none. Therefore
`HasReachableRoots 1` is false.

This is a direct counterexample to the *redundancy of the
extra hypothesis*, not a counterexample to EPPA itself.
The Lean application theorem remains correct and quite
substantial; it simply does not imply Theorem 12.9 in the
stated generality.

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
- Settle unrooted d-closure k-orientations, preferably with
  a separate reader-facing theorem over arbitrary k-orientations.
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
or a logical contradiction. The reported application gap is
a gap between a valid *narrower* theorem and a broader
published statement. Equally, the AP/SAP discrepancy is
already mitigated by a separate stronger Lean theorem
that avoids the public facade's extra restriction.
