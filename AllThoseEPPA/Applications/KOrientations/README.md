# Rooted k-orientations with d-closures — Lean application

**Status: the actual full d(A) theorem is proved.** The dedicated [application PR #242](https://github.com/shulda/lean_all_those_eppa_classes/pull/242) contains the original positive-arity d-closure EPPA application from Section 9.3 (`thm:DF`) of *All those EPPA classes*. The combined application commit `eeea61348615` passed the [complete Lean build and allowed-axioms audit](https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/38926049553) on 2026-10-16.

**For downstream use**, import `AllThoseEPPA.KOrientationsEPPA` and read [`K_ORIENTATIONS_EPPA_API.md`](../../../K_ORIENTATIONS_EPPA_API.md). The original theorem is:

```lean
AllThoseEPPA.Applications.KOrientations.exists_rootedKOrientation_faithfulCoherentDEPPa
```

It is a finite rooted **k-orientation** theorem: every point must be able to reach an outdegree-<k root. The witness remains finite, rooted, and of outdegree at most k; its **original full** higher-arity `dStructure` embedding has coherent EPPA and irreducible-structure faithfulness. Unrooted orientations and unoriented reducts are not covered by this theorem.

## Overview

The proof deliberately uses two separate applications of the general faithful coherent EPPA theorem, since the **actual d-language includes function symbols of every positive arity** and cannot be passed to the general unary-function theorem directly.

- **First stage — successor language.** `Graph.lean`, `Closures.lean`, `Encoding.lean`, `StructureBridge.lean`, and `FirstWitness.lean` encode the original graph by its set-valued unary successor operation. `SuccessorFaithful*.lean`, `FaithfulOutdegree.lean`, and `FirstStageInClass.lean` prove that the unrestricted first witness is **exactly** the successor structure of a genuine finite bounded-outdegree orientation. The original source need not have a d-closed image in this successor witness.
- **Second stage — root language.** `AuxiliaryLanguage.lean`, `GraphAutomorphismGroup.lean`, `AuxiliaryAction.lean`, `SecondWitness.lean`, and the `SelectedSecond*.lean` files construct the auxiliary Γ-root language and choose another finite coherent faithful witness. The group Γ can be `Aut(G)` with genuinely **nontrivial language-symbol action**, including the κ component.
- **Reconstruction.** `ReconstructionCarrier.lean` and the associated `Reconstruction*.lean`, `RootMatching*.lean` and `SourceReconstruction*.lean` modules build a finite orientation using canonical entire root supports, with the exact edge and root-set correspondence. `ReconstructionRootedDResult.lean` proves the reconstructed graph again has the required rooted d-closure structure.
- **Original all-arity embedding.** `SourceSupportedDTraceIso.lean`, `FirstStageFullDSourceEmbedding.lean`, `OriginalDReconstructedEmbedding.lean` and `OriginalDFaithfulReconstruction.lean` construct and certify an exact embedding of the **original** entire d(A), not just a conveniently supported surrogate. `SelectedOriginalRootGluing.lean` and `SelectedOriginalNonrootGluing.lean` give separate pointwise ExtendsAlong squares for every old domain vertex.
- **Coherence and final selection.** `SelectedReconstructedCoherence.lean`, `SelectedOriginalFullDExtendsAlong.lean` and `SelectedOriginalFullDCoherentExtension.lean` show both real selected automorphism families induce one public coherent-extension operation on ALL original d-partial isomorphisms. `RootedKOrientationDFinalEPPA.lean` combines them with the two existential witness constructions and verifies witness finiteness, rootedness, coherent EPPA and irreducible-structure faithfulness.

## Mathematical pitfalls explicitly addressed

1. The `dStructure` has genuine symbols `F_n` for every `n≥1`; they are not unary functions disguised as higher-arity notation.
2. The original old vertex image in the first successor witness is successor-closed; it is **not assumed** to be ambient d-closed.
3. The second Γ-auxiliary-language automorphisms are allowed to move relation symbols. Discarding the κ group-language component would make the coherent composition assertion false.
4. A freshly reconstructed nonroot vertex carries its full canonical root support and a canonical centre. Distinct old vertices are not identified by arbitrary representative selection.
5. The actual original d(A) embedding is the same one for which coherent EPPA and irreducible-structure faithfulness are proved. Both roots and nonroots of original partial-domain maps are handled.

## Use and audit

- Supported import and exact formal theorem statement: [public API](../../../K_ORIENTATIONS_EPPA_API.md).
- Import-only regression for consumers: [`Examples/KOrientationsDFPublicAPIUsage.lean`](../../Examples/KOrientationsDFPublicAPIUsage.lean).
- Authoritative original source theorem: [`RootedKOrientationDFinalEPPA.lean`](RootedKOrientationDFinalEPPA.lean).
- Stable general theorem API, **distinct from this large application**: [`MainTheorems.lean`](../../MainTheorems.lean).
- Dedicated application branch: [PR #242](https://github.com/shulda/lean_all_those_eppa_classes/pull/242).
- Verified final all-arity theorem on the application branch: [full Lean CI 38926049553](https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/38926049553). The public import and its smoke test undergo a further separate CI run before integration.

The proof uses no application-specific axioms, `sorry` or `admit`. The CI's allowed axiom set remains `propext`, `Classical.choice`, and `Quot.sound`. All testing is in the **public Lean repository**, never in the private manuscript repository.
