import AllThoseEPPA.Applications.KOrientations.ReconstructionRootSupportCriterion
import AllThoseEPPA.Applications.KOrientations.Encoding

/-!
# A precise d-fibre criterion for the reconstructed graph

Once the reconstructed roots are exactly the B₁-root sort and the
reachable roots of every vertex equal its intrinsic tagged support,
the entire family of non-unary d-functions is determined without any
further arbitrary choice. This file isolates the *exact* remaining
hypotheses rather than claiming them before the localization proof.

In particular, positive-arity fibres on tuples of distinct root-sort
vertices consist precisely of all reconstructed vertices with the
prescribed intrinsic support. This will turn a local support-preserving
bijection of closed pieces into an isomorphism in the full d-language.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- On a reconstructed oriented graph with the intended root status
and exact root supports, the d-fibre test has the canonical
support-only form, uniformly in every arity n. -/
theorem faithful_reconstructed_dFiber_iff_intrinsicSupport
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (hRootSort : ∀ z : ReconstructedCarrier G k B,
      (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k z ↔
        ∃ r : W, z = Sum.inl r)
    (hRoots : ∀ z : ReconstructedCarrier G k B,
      (faithfulReconstructedDigraph G k S B ι hFaith).roots k z =
        (Sum.inl : W → ReconstructedCarrier G k B) ''
          reconstructedSupport G k B z)
    (n : ℕ) (xs : Fin n → ReconstructedCarrier G k B)
    (z : ReconstructedCarrier G k B) :
    z ∈ (faithfulReconstructedDigraph G k S B ι hFaith).dFiber k xs ↔
      0 < n ∧
      Function.Injective xs ∧
      (∀ i : Fin n, ∃ r : W, xs i = Sum.inl r) ∧
      ((Sum.inl : W → ReconstructedCarrier G k B) ''
        reconstructedSupport G k B z) = Set.range xs := by
  change
    (0 < n ∧ Function.Injective xs ∧
      (∀ i, (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k
        (xs i)) ∧
      (faithfulReconstructedDigraph G k S B ι hFaith).roots k z =
        Set.range xs) ↔ _
  constructor
  · rintro ⟨hn, hinj, hr, hset⟩
    refine ⟨hn, hinj, ?_, ?_⟩
    · intro i
      exact (hRootSort (xs i)).mp (hr i)
    · exact (hRoots z).symm.trans hset
  · rintro ⟨hn, hinj, hr, hset⟩
    refine ⟨hn, hinj, ?_, ?_⟩
    · intro i
      exact (hRootSort (xs i)).mpr (hr i)
    · exact (hRoots z).trans hset

/-- The same criterion is the literal interpretation of the
corresponding positive-arity function in the checked full d-language. -/
theorem faithful_reconstructed_dStructure_fiber_iff
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (hRootSort : ∀ z : ReconstructedCarrier G k B,
      (faithfulReconstructedDigraph G k S B ι hFaith).IsRoot k z ↔
        ∃ r : W, z = Sum.inl r)
    (hRoots : ∀ z : ReconstructedCarrier G k B,
      (faithfulReconstructedDigraph G k S B ι hFaith).roots k z =
        (Sum.inl : W → ReconstructedCarrier G k B) ''
          reconstructedSupport G k B z)
    (n : ℕ) (hpos : 0 < n)
    (xs : Fin n → ReconstructedCarrier G k B)
    (z : ReconstructedCarrier G k B) :
    z ∈ (dStructure
      (faithfulReconstructedDigraph G k S B ι hFaith) k).func
        (DFunctionSymbol.fiber n hpos) xs ↔
      Function.Injective xs ∧
      (∀ i : Fin n, ∃ r : W, xs i = Sum.inl r) ∧
      ((Sum.inl : W → ReconstructedCarrier G k B) ''
        reconstructedSupport G k B z) = Set.range xs := by
  change z ∈
    (faithfulReconstructedDigraph G k S B ι hFaith).dFiber k xs ↔ _
  rw [faithful_reconstructed_dFiber_iff_intrinsicSupport
    G k S B ι hFaith hRootSort hRoots n xs z]
  simp only [hpos, true_and]

end AllThoseEPPA.Applications.KOrientations
