import AllThoseEPPA.Applications.KOrientations.SelectedSecondAuxCoherentExtension
import AllThoseEPPA.Applications.KOrientations.ReconstructionVertexAction

/-!
# Genuine second selected extension commutes with source root embedding

For the actual original full all-arity d(A) partial map p, the
first coherent EPPA selector produces the exact Γ-root partial
automorphism a_p of the auxiliary root structure. The SECOND
coherent selector yields a TOTAL automorphism f_p of B₁.

The real public ExtendsAlong equation gives TWO indispensable
facts, neither of which can be discarded:
* f_p.lang * κ.lang = κ.lang * a_p.lang in the true B₀
  graph automorphism group (the second source embedding may have
  nonidentity group label);
* on EVERY actual closed root-domain vertex x of a_p,
  f_p (κ x) = κ (a_p x).

The choice-free reconstructed vertex permutation acts by f_p
on the root sort, so this is exactly the first direct gluing
equation for the genuine second-stage source root embedding.
This does NOT yet prove that the nonroot reconstructed vertices
extend p nor the final full d-coherent EPPA theorem.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v w

/-- Exact group/language-component compatibility for the ACTUAL
second selected B₁ automorphism. The second-stage embedding
κ can carry a nonidentity graph-group component. -/
theorem firstStage_selectedSecondAuxExtension_lang_gluing
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (t : Structure.CoherentExtension (auxiliaryAction G k) κ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k)) :
    (firstStage_selectedSecondAuxExtension A G k ι s B κ t p).lang *
        κ.lang =
      κ.lang *
        (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p).lang :=
  (firstStage_selectedSecondAuxExtension_extendsRoot
    A G k ι s B κ t p).1

/-- The ACTUAL selected root vertex map extends the exact
first selected Γ-root partial map at every point of its genuine
closed source domain, retaining the second embedding κ. -/
theorem firstStage_selectedSecondAuxExtension_root_gluing
    {V : Type u} {W : Type v} {X : Type w}
    [Fintype V] [Fintype W] [Fintype X]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (s : Structure.CoherentExtension successorAction ι)
    (B : Structure (auxiliaryLanguage G k) X)
    (κ : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k (Set.range ι.toFun)) B)
    (t : Structure.CoherentExtension (auxiliaryAction G k) κ)
    (p : Structure.PartialAutomorphism dTrivialAction (dStructure A k))
    (x : RootsIn G k (Set.range ι.toFun))
    (hx : x ∈ (firstStage_selectedAuxRootPartialAutomorphism
      A G k ι s p).source) :
    reconstructedVertexPerm G k B
      (firstStage_selectedSecondAuxExtension A G k ι s B κ t p)
      (Sum.inl (κ x)) =
      Sum.inl (κ (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p x)) := by
  change Sum.inl
      (firstStage_selectedSecondAuxExtension A G k ι s B κ t p (κ x)) =
    Sum.inl (κ (firstStage_selectedAuxRootPartialAutomorphism A G k ι s p x))
  exact congrArg Sum.inl
    ((firstStage_selectedSecondAuxExtension_extendsRoot
      A G k ι s B κ t p).2 x hx)

end AllThoseEPPA.Applications.KOrientations
