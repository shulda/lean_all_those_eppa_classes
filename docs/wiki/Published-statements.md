# Published mathematical statements versus Lean declarations

**Reference:** Hubička–Konečný–Nešetřil, *All those EPPA classes*
([public paper](https://arxiv.org/abs/1902.03855)). This is a
source-to-code audit of
[commit `d85fda061d0b`](https://github.com/shulda/lean_all_those_eppa_classes/commit/d85fda061d0b43f2b78c2470ce51f16ecf5c4e8d)
and the 16 October 2026 green full CI.
The author's private/current Overleaf source is **not** verified here.
If its statement numbers or hypotheses differ, this crosswalk must be updated.

## Interpretation of statuses

- **Verified endpoint, scope consistent:** a concrete Lean declaration is
  proved, and the inspected source statement appears to be covered.
  This is a mathematical-reading verdict, not a second kernel proof.
- **Verified stronger form:** Lean proves a statement with weaker inputs or
  stronger outputs; the printed case follows.
- **Verified narrower form:** the present Lean endpoint requires an
  additional assumption or drops a printed conclusion. It is *not* an
  exact formalization of the printed assertion.
- **Not yet independently matched:** no specific public endpoint was
  verified in this audit. This does not assert mathematical falsehood
  or absence from every internal file.

## The main construction and transfer theorems

| Printed item | Lean declaration | Comparison |
| --- | --- | --- |
| Theorem 1.1, `thm:nreppa` | [`MainTheorems.unrestrictedFaithfulCoherentEPPA`](../../AllThoseEPPA/MainTheorems.lean) | **Scope consistent.** Finite Γ-structure with unary set-valued function symbols and finite relabelling orbit; finite coherent EPPA witness, irreducible-structure faithful |
| Theorem 1.2, `thm:maintree` | [`MainTheorems.restrictedLocallyTreeLikeEPPA`](../../AllThoseEPPA/MainTheorems.lean) | **Verified stronger form.** An arbitrary finite starting EPPA witness, global homomorphism-embedding back, every closed n-small substructure maps to a tree amalgamation of full A-copies, faithfulness, conditional coherence. Lean allows n=0 and does not require A itself irreducible, unlike the printed version |
| Theorem 1.5, `thm:main` (Herwig–Lascar generalization) | [`MainTheorems.herwigLascar`](../../AllThoseEPPA/MainTheorems.lean) | **Verified stronger form in ambient cardinality.** N is an arbitrary type in Lean rather than just finite/countable. Finite forbidden family means Γ-homomorphism-embedding avoidance, not induced-copy avoidance |
| Theorem 1.6, `thm:mainstrong` (ordinary and coherent locally finite transfer) | [`MainTheorems.locallyFiniteEPPA`, `locallyFiniteCoherentEPPA`](../../AllThoseEPPA/MainTheorems.lean) | **Scope consistent.** The printed Theorem 1.6 explicitly requires a hereditary subclass of irreducibles with the **strong amalgamation property (SAP)**, along with locally finite automorphism-preserving completion. The Lean facade expresses these. The independently verified [AP-level core theorem](../../AllThoseEPPA/StrongCompletionManuscriptSubclass.lean) is a strengthening, not a repair of the published theorem |
| Proposition 11.3, `prop:strongcompletion` | [`MainTheorems.completionIffStrong`](../../AllThoseEPPA/MainTheorems.lean) | **Scope consistent.** For hereditary finite SAP classes, ordinary homomorphism-embedding completions exist iff injective ones exist; no automorphism-preserving lift is concluded |

Theorem 1.2's projection is a **homomorphism-embedding**, not necessarily
an induced embedding on the entire constructed structure; small closed
substructures map to actual trees of **full copies of A**, not arbitrary
clique covers. Theorem 1.6 uses the full locally finite
*automorphism-preserving* completion predicate of Definition 11.2,
not merely local completion of bounded sets.

Theorem 1.1 handles genuinely nontrivial permutations of relation and
function symbols; the `HasFiniteRelabelOrbit` assumption must not be
silently dropped when Γ is infinite.

## Other parts of the paper

| Printed item | Audited Lean status | Qualification |
| --- | --- | --- |
| Proposition 2.5/2.6 definitions of EPPA and coherent triples | [`EPPA.lean`](../../AllThoseEPPA/EPPA.lean), [`PartialIso.lean`](../../AllThoseEPPA/PartialIso.lean) | Checked exact extension square, domain-range composition, and selection coherence |
| Proposition `prop:setcoherence` | `AllThoseEPPA.finiteSetsHaveCoherentEPPA` | Verified per the [project status ledger](../../FORMALIZATION.md) |
| Relational and infinite-language valuation statements | `Relational.finiteRelationalStructuresHaveCoherentEPPA` and `InfiniteRelational.finiteOrbitRelationalStructuresHaveCoherentEPPA` | Verified per the status ledger; a full independent formula-by-formula audit is not recorded here |
| Unary functions `prop:eppafunctions` | `UnaryFunctions.finiteOrbitUnaryStructuresHaveCoherentEPPA` | Verified per the status ledger |
| Faithfulness `prop:faithful` and sparsening `lem:sparsen` | [`FaithfulProposition.lean`](../../AllThoseEPPA/FaithfulProposition.lean), [`CycleSparseningTheorem.lean`](../../AllThoseEPPA/CycleSparseningTheorem.lean) | Constructive verified endpoints; see proof architecture |
| Theorem 1.3 and Corollary 1.4 | — | No dedicated public endpoint verified in this crosswalk; distinguish a consequence of general results from an exported proof of the exact numbered statement |
| Proposition 12.2, finite metric spaces with forbidden unit clique | [`IntegerMetric.Bridge.allFiniteBoundedMetricsHaveEPPAAndPreserveUnitClique`](../../AllThoseEPPA/Examples/IntegerMetricAllDMainTheorem.lean) | **Not the identical printed proposition.** Lean supplies *ordinary* EPPA with an arbitrary fixed finite integer distance bound D, preserving maximum unit-clique size; the printed application asserts coherent EPPA for the corresponding class without a prescribed global D |
| Theorem 12.12, d-closures of k-orientations (Section 12.5, Definition 12.10) | [`KOrientationsEPPA.rootedFaithfulCoherent`](../../AllThoseEPPA/KOrientationsEPPA.lean) | **Scope consistent, including rootedness.** The printed class `D_d^k` is defined **only** for `s(G) ∈ D_{s+}^k`, which means every vertex has a reachable root. Lean spells this out as `HasReachableRoots k`, and proves genuine full all-arity d-closure coherent irreducible-structure faithful EPPA. The paper states k ≥ 1; the Lean statement takes a natural k |
| Other applications, including constants and other k-orientation formulations | — | Must not be described as formalized solely because the general machinery is available; check exact source-facing declarations first |

## Checking the class definition before the theorem

The public [paper, arXiv:1902.03855v4, printed pp. 51–52](https://arxiv.org/pdf/1902.03855)
contains three distinct objects:

1. **Definition 12.9:** `s(G)` is a unary-successor expansion
   of an arbitrary finite k-orientation, with reachable vertices
   (including the starting vertex) as the unary function values.
2. The subclass `D_{s+}^k` is then defined by
   `roots_G(x) ≠ ∅` **for every vertex x**. A root means
   out-degree strictly smaller than k.
3. **Definition 12.10:** `D_d^k := {d(G) : s(G) ∈ D_{s+}^k}`.
   Higher-arity `F_n` return vertices whose reachable-root set
   is precisely the given tuple of distinct roots.
   **Theorem 12.12** establishes coherent, irreducible-structure
   faithful EPPA for *that already restricted class*.

The corresponding Lean source in
[`Graph.lean`](../../AllThoseEPPA/Applications/KOrientations/Graph.lean)
uses `HasReachableRoots k`; the exact root-fibre semantics
are in [`Closures.lean`](../../AllThoseEPPA/Applications/KOrientations/Closures.lean)
and [`Encoding.lean`](../../AllThoseEPPA/Applications/KOrientations/Encoding.lean).
These are the paper's hypotheses, not a weakening of the result.

For example, the oriented 3-cycle is a 1-orientation with no roots,
so it belongs to `D^1` but **not** to the class `D_d^1`
defined in the paper. The authors explicitly explain that
rootless vertices would enter the closure of the empty set
and would require constants, which they leave out.

An earlier draft of this wiki incorrectly described the condition
as an *extra Lean hypothesis*. The correction is recorded in
[Adversarial audit](Adversarial-audit.md). No unrooted-case
reduction is required to justify the published theorem.

## Reading the current state

For the canonical names and the consumer-facing theorem types, use
[`AllThoseEPPA/MainTheorems.lean`](../../AllThoseEPPA/MainTheorems.lean)
and [`MAIN_THEOREMS_API.md`](../../MAIN_THEOREMS_API.md).
The [adversarial audit](Adversarial-audit.md) tracks what remains
to be checked rather than treating omissions as proved results.
