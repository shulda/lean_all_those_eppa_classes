import AllThoseEPPA.Applications.KOrientations.SelectedOriginalFullDCoherentExtension
import AllThoseEPPA.Applications.KOrientations.FirstStageInClass
import AllThoseEPPA.Applications.KOrientations.SecondWitness
import AllThoseEPPA.Applications.KOrientations.ReconstructionRootedDResult

/-!
# Finite coherent and irreducible-faithful EPPA for k-orientations with d-closures

The first EPPA construction is applied to the genuine successor encoding
of a finite rooted k-orientation A. Its faithful coherent witness is
proved to be exactly the successor structure of a finite k-orientation
G, so the original chosen embedding and coherent selector are retained.
No erroneous assumption that the original source image is ambient
d-closed in G is made.

Apply the certified unrestricted faithful coherent EPPA theorem a SECOND
time to the true auxiliary Γ-root structure of G, with Γ=Aut(G)
and its generally NONTRIVIAL action. From the finite second witness
construct the genuinely finite choice-free reconstructed k-orientation
with canonical nonroot vertices (centre, whole root support). Its
rootedness and correct full arbitrary positive-arity set-valued
d-language follow from the verified support-path construction.

The actual original d(A) is embedded by a genuine full-language
Structure.Embedding into this reconstructed orientation's d-structure,
and both selected total extension stages induce one PUBLIC coherent
EPPA extension on the ORIGINAL domain. The same embedding is
irreducible-structure faithful. This theorem is the final existence
form of the reconstructed k-orientation d-closure EPPA application,
conditional only on finite input rooted k-orientation assumptions.
Verified by the full Lean library build and allowed-axioms audit
on the original exact candidate and on the integrated application
draft (2026-10-16, commit eeea61348615; Actions run 38926049553).
The proof states no EPPA theorem for arbitrary unrooted orientations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

/-- Every finite rooted k-orientation admits a finite rooted
k-orientation witness for the ENTIRE genuine d-closure language
(all set-valued F_n, n>=1), with a coherent extension of all
partial automorphisms and genuine irreducible-structure
faithfulness of the original full d(A) embedding. -/
theorem exists_rootedKOrientation_faithfulCoherentDEPPa
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
      Structure.IsIrreducibleStructureFaithful dTrivialAction ψ := by
  classical
  obtain ⟨W, hFinW, H, B₀, ι, hB₀, hC₀, hFaith₀⟩ :=
    exists_firstStageKOrientationWitness A k hBound
  letI : Fintype W := hFinW
  obtain ⟨s⟩ := hC₀
  subst B₀
  obtain ⟨X, hFinX, B₁, κ, hC₁, hFaith₁⟩ :=
    exists_secondStageUnrestrictedWitness H.graph k (Set.range ι.toFun)
  letI : Fintype X := Fintype.ofFinite X
  obtain ⟨t⟩ := hC₁
  let S : Set W := Set.range ι.toFun
  let K : KOrientation (ReconstructedCarrier H.graph k B₁) k :=
    faithfulReconstructedKOrientation
      H.graph k S H.bound B₁ κ hFaith₁
  have hKRooted : K.graph.HasReachableRoots k :=
    (faithful_reconstructed_exact_roots_and_rooted
      H.graph k S H.bound
      (successorEmbedding_image_successorClosed A H.graph ι)
      (successorEmbedding_image_rooted A H.graph k hRooted ι)
      B₁ κ hFaith₁).1
  have hCoherentFaithful :=
    firstStage_originalDReconstructed_coherentFaithful
      A H.graph k H.bound hRooted ι s B₁ κ t hFaith₁
  refine ⟨ReconstructedCarrier H.graph k B₁,
    inferInstance, K,
    firstStage_originalDReconstructedEmbedding
      A H.graph k H.bound hRooted ι B₁ κ hFaith₁,
    hKRooted, ?_, ?_⟩
  · exact hCoherentFaithful.1
  · exact hCoherentFaithful.2

end AllThoseEPPA.Applications.KOrientations
