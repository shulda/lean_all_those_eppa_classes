import AllThoseEPPA.Applications.KOrientations.SourceReconstructionVertex

/-!
# The source-copy construction is independent of root enumerations

The canonical reconstructed nonroot is determined by its transported
centre and its unordered set of realized roots. Therefore *any*
two source R_P realizations of the same vertex give precisely the
same reconstructed vertex. In particular, sourceReconstructedVertex
does not depend mathematically on the noncomputable pattern selected
by Classical.choice.

This is the reusable replacement for a quotient-transversal argument.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

namespace SourceNonrootPattern

variable {V : Type u} [Fintype V] {W : Type v}
variable {G : Digraph V} {k : ℕ} {S : Set V} {x : V}

/-- The transported canonical pair does not depend on the choice
of source relation label or of its root enumeration. -/
theorem toCanonical_eq_of_same_center
    (d e : SourceNonrootPattern G k S x)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    d.toCanonical B ι = e.toCanonical B ι := by
  apply CanonicalNonroot.eq_of_center_support
  · rw [d.toCanonical_center, e.toCanonical_center]
  · rw [d.toCanonical_support_eq, e.toCanonical_support_eq]

end SourceNonrootPattern

/-- The source-copy vertex map agrees with *any* realized source
R_P pattern of a nonroot, not merely the selected one. -/
theorem sourceReconstructedVertex_eq_of_pattern
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (x : {v : V // v ∈ S})
    (hNotRoot : ¬ G.IsRoot k x.val)
    (d : SourceNonrootPattern G k S x.val) :
    sourceReconstructedVertex G k S hClosed hRooted B ι x =
      (.inr (d.toCanonical B ι) :
        ReconstructedCarrier G k B) := by
  simp only [sourceReconstructedVertex, dif_neg hNotRoot]
  congr 1
  exact SourceNonrootPattern.toCanonical_eq_of_same_center
    (chosenSourceNonroot G k S hClosed hRooted
      x.val x.property hNotRoot) d B ι

end AllThoseEPPA.Applications.KOrientations
