# EPPA for finite rooted k-orientations with d-closures

**Article:** *All those EPPA classes*, Section 9.3, `thm:DF` (the oriented, rooted d-closure application).

**Public Lean import:**

```lean
import AllThoseEPPA.KOrientationsEPPA
```

This application is **proved and Lean-checked**, not an axiom and not an application of the unary EPPA theorem directly to the higher-arity d-language. The complete original existence theorem was independently compiled on the [application draft commit `eeea61348615`](https://github.com/shulda/lean_all_those_eppa_classes/commit/eeea61348615e65f81457a5371d8262a48046c6c), [CI run 38926049553](https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/38926049553) (full Lean build and permitted-axioms audit). The public facade and consumer regression must pass their own CI before being treated as integrated.

## Exact theorem and assumptions

In namespace `AllThoseEPPA.Applications.KOrientations`:

```lean
exists_rootedKOrientation_faithfulCoherentDEPPa
```

The public wrapper is `AllThoseEPPA.KOrientationsEPPA.rootedFaithfulCoherent`:

```lean
theorem rootedFaithfulCoherent
    {V : Type u} [Fintype V]
    (A : Digraph V) (k : ℕ)
    (hBound : A.HasOutdegreeAtMost k)
    (hRooted : A.HasReachableRoots k) :
    ∃ (W : Type u) (_ : Fintype W)
      (K : KOrientation W k)
      (ψ : Structure.Embedding dTrivialAction
        (dStructure A k) (dStructure K.graph k)),
      K.graph.HasReachableRoots k ∧
      Structure.IsCoherentEPPAWitness dTrivialAction ψ ∧
      Structure.IsIrreducibleStructureFaithful dTrivialAction ψ
```

Here `Digraph` is oriented: its edge relation has no loops and no antiparallel pairs. `HasOutdegreeAtMost k` is the **actual** outdegree bound, and `HasReachableRoots k` requires every vertex to reach some vertex of outdegree **strictly less than** `k`, via a directed path of length at least zero. A root is not defined as an outdegree-zero vertex unless `k = 1`. The output `K : KOrientation W k` again has the actual bound, with rootedness stated separately. Both carrier types are finite, and `ψ` is a genuine exact embedding of the ORIGINAL `dStructure A k`, not an embedding of a surrogate induced chart.

The `dStructure` language has (i) a set-valued unary successor symbol encoding directed reachability and (ii) real set-valued symbols `Fₙ` for **every positive arity**. These include root-fibre closure information. `Structure.IsCoherentEPPAWitness` means there is a single extension selector for *every* original partial automorphism; it extends along `ψ`, respects equivalent partial maps and composes on coherent triples. `Structure.IsIrreducibleStructureFaithful` is about **the same original embedding `ψ`**.

The facade also provides `rootedFaithfulOrdinary` with `Structure.IsEPPAWitness` instead of the coherent clause; ordinary EPPA is obtained by forgetting the verified coherence of the actual witness, with no change of output class or embedding.

## Use in another Lean project

Add the public repository as a Lake dependency, pinning a known-green commit that includes this application. For example, in `lakefile.toml`:

```toml
[[require]]
name = "AllThoseEPPA"
git = "https://github.com/shulda/lean_all_those_eppa_classes.git"
rev = "<verified-commit-with-k-orientations>"
```

This repository currently uses Lean `v4.34.1` and Mathlib `v4.34.1`. Consumers can import just `AllThoseEPPA.KOrientationsEPPA`; no need to import the umbrella `AllThoseEPPA` or internal reconstruction files.

The [import-only consumer smoke test](AllThoseEPPA/Examples/KOrientationsDFPublicAPIUsage.lean) uses both public entry points and extracts the rooted finite ordinary witness while retaining irreducible-structure faithfulness.

## Proof architecture (what is actually certified)

1. `FirstStageInClass.lean` recovers the successor structure of a genuine bounded-outdegree orientation from the first unrestricted faithful coherent EPPA witness, with its exact language interpretation.
2. `SecondWitness.lean` applies the unrestricted theorem again to the real auxiliary root structure over `Γ = Aut(G)`. Its relation-language action is generally **nontrivial**; the proof never silently trivializes the associated symbol component.
3. `ReconstructionCarrier.lean`, `ReconstructedDigraph.lean`, `ReconstructionRootedDResult.lean` and related support/closure files produce the finite reconstructed rooted orientation. A nonroot vertex uses its canonical entire root support, not a choice of arbitrary root representatives.
4. `OriginalDReconstructedEmbedding.lean` embeds the true original all-arity d-structure. Its old image in the first successor witness is **successor-closed**, but need not be ambient **d-closed**. The proof explicitly avoids this false assumption.
5. `OriginalDFaithfulReconstruction.lean` proves irreducible-structure faithfulness of that exact original embedding. `SelectedOriginalRootGluing.lean` and `SelectedOriginalNonrootGluing.lean` verify the extension square for actual old root and nonroot points respectively.
6. `SelectedOriginalFullDExtendsAlong.lean` and `SelectedOriginalFullDCoherentExtension.lean` assemble the selected total automorphisms into a public coherent extension for all original positive-arity d-partial maps, with Equivalent and ordered coherent-triple preservation.
7. `RootedKOrientationDFinalEPPA.lean` existentially selects BOTH finite first and second witnesses and checks the **entire** claim, including membership in the rooted k-orientation class.

## Verification and scope

The authoritative compiled application result is on the [dedicated draft PR #242](https://github.com/shulda/lean_all_those_eppa_classes/pull/242), which keeps the long k-orientation proof separate from the reusable general EPPA library until final integration. Its full theorem source is [`RootedKOrientationDFinalEPPA.lean`](AllThoseEPPA/Applications/KOrientations/RootedKOrientationDFinalEPPA.lean). The final clean draft source merged the independently checked selected-automorphism, source embedding, faithful, and existential-existence proof modules via PR #289.

**Not claimed:** EPPA for unrestricted unrooted k-orientations, EPPA for an unoriented reduct obtained by forgetting orientations, or a computation of optimal witness size. Nothing in this application changes the assumptions of the reusable main theorems or proves arbitrary relational/function-language EPPA beyond their stated scope.

For the generic EPPA theorems (unrestricted, locally tree-like, Herwig–Lascar, local-finiteness transfer), see [`MAIN_THEOREMS_API.md`](MAIN_THEOREMS_API.md). For the metric and clique-preserving regression, see [`INTEGER_METRIC_EPPA_API.md`](INTEGER_METRIC_EPPA_API.md).
