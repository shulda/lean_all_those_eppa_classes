# \(k\)-orientations with \(d\)-closures: Lean application

This directory contains the **large, separately organized application**
of the main EPPA theorems to finite \(k\)-orientations with
successor- and root-fibre closures (the oriented theorem `thm:DF`
of *All those EPPA classes*).

The paper and mathematical audit live in the private manuscript repo:
[`K_ORIENTATIONS_AUDIT_2026-10-12.md`](https://github.com/shulda/Eppouzy---formalizace/blob/audit-k-orientations-d-closures-20261012/K_ORIENTATIONS_AUDIT_2026-10-12.md).
The proposed Lean architecture and choice-free reconstruction are:
[`K_ORIENTATIONS_LEAN_DESIGN.md`](https://github.com/shulda/Eppouzy---formalizace/blob/audit-k-orientations-d-closures-20261012/K_ORIENTATIONS_LEAN_DESIGN.md).

## Files and responsibility

| Module | Responsibility |
| --- | --- |
| [`Graph.lean`](Graph.lean) | Oriented graph, reflexive directed paths, exact outdegree, roots, root-set monotonicity |
| [`Closures.lean`](Closures.lean) | Set-valued successor closure and all arity-indexed \(F_n\)-fibres, closure criterion, closedness |
| [`ClosureMinimal.lean`](ClosureMinimal.lean) | Least \(d\)-closed superset theorem via an explicit enumeration of every vertex's entire nonempty root set |
| [`../KOrientations.lean`](../KOrientations.lean) | Application-level import, used by the root library for regression checking |

The target \(d\)-structure has **infinitely many function symbols**
\(F_n\) (\(n\ge1\)). The general public EPPA theorem applies **only to
unary-function languages**. Accordingly, it must be invoked on the
successor-closure structure and on a finite auxiliary root language,
not directly on the \(d\)-expansion. Pretending that \(F_n\) are unary
would invalidate the application.

## Auxiliary root language

The source module `AuxiliaryLanguage.lean` introduces the full non-root template labels with ordered, pairwise distinct root tuples, their arity-indexed `R_P` / `E_P` relation symbols, and the root-only auxiliary structure. Its only function symbol is unary, making it eligible for the public unrestricted EPPA theorem after the symbol-action step.

## Faithful local transfer and pattern equivariance

`FaithfulLocalTransfer.lean` packages one-point and relation-tuple closure transportation by irreducible-structure faithfulness. `PatternTransport.lean` formalizes how a root-pattern label changes under a permutation preserving root status and complete root sets. Both are prerequisites for deriving the first witness's structural axioms and for the nontrivial auxiliary symbol action.

## Orienting the faithful witness

`SuccessorFaithfulGraph.lean` uses genuine irreducible-structure faithfulness and graph-relation transport to prove the raw first-stage witness has no antiparallel edges or loops. This reconstructs its directed graph without assuming that unrestricted EPPA preserves the class. The bounded outdegree and exact unary successor interpretation remain open obligations.

## Faithful edge/successor compatibility

`SuccessorFaithfulFunctions.lean` shows that, in the faithful first-stage witness, every directed edge points to a vertex in the source's unary successor closure. This is a local compatibility theorem, not yet the converse equality with full graph reachability.

## Unary successor reflexivity

`SuccessorFaithfulUnary.lean` proves every unary function value stays in the associated one-point closure, and that every vertex belongs to its own successor value in an irreducible-structure faithful first-stage witness. Both are needed to reconstruct exact reachability.

## Transitivity of unary successor values

`SuccessorFaithfulTransitive.lean` transports vertices of a one-point closure into the original successor structure, proves membership transport under automorphisms/embeddings, and establishes the unary function's transitivity F(F(x)) ⊆ F(x).

## Transporting directed paths

`FaithfulReachability.lean` shows that directed paths in the source graph are preserved by the exact embedding into the first faithful witness, and that total witness automorphisms preserve graph reachability. This enables the reverse inclusion between the witness's unary successor function and graph-theoretic reachability.

## First invocation of the main theorem

The `FirstWitness.lean` file now applies the checked unrestricted irreducible-structure faithful coherent EPPA theorem to the successor language with trivial group action. The witness is intentionally named *unrestricted*: proving its membership in the successor-closure k-orientation class is a separate remaining obligation, not part of the general EPPA theorem.

## Next mathematical layers

1. Encode \(s(G)\) and \(d(G)\) as actual `AllThoseEPPA.Structure` objects, using the exact set-valued-function semantics from `Structure.lean`.
2. Prove the \(s\)-class is free-amalgamating and get \(B_0\) using `MainTheorems.unrestrictedFaithfulCoherentEPPA` plus the irreducible-structure-faithful free-amalgamation transfer.
3. Build finite relation symbols \(R_P,E_P\) and the \(\Gamma\)-root structure \(A_1\), preferably taking \(\Gamma=\operatorname{Aut}(B_0)\) itself as a nonfaithful symbol action.
4. Apply the **second** unrestricted faithful coherent EPPA theorem to get \(B_1\).
5. Implement the choice-free reconstructed vertices \((x,W)\), their canonical root matching, four edge clauses, and automorphisms.
6. Establish \(B\in \mathcal D_d^k\), irreducible-structure faithfulness, EPPA, then coherence.
7. Add a readable final theorem and a small consumer smoke test.

## Verification policy

- New proof declarations should have explicit proof terms or `by` scripts. No `sorry`, `admit`, or application-specific axioms.
- **Do not claim the full theorem is proved until the final result type is inhabited and compiled.**
- The dedicated branch is developed as a draft PR. The existing CI for the **public Lean** repository is the project's already configured build mechanism; no workflows are added.
- No GitHub Actions are to be used or created in the **private manuscript** repository. TeX compilation there is local-only.
- Initial modules are authored here but require Lean/Mathlib compilation; the assistant's current sandbox has neither Lean installed nor network access to install it. Keep their status distinct from the already certified general EPPA API.

The current scaffold is not a statement of EPPA for unoriented
reducts. The possible relationship with EHN's \(\mathcal G_F\) is
deliberately deferred.
