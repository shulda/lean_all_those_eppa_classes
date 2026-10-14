import AllThoseEPPA.Applications.KOrientations.SourcePatternRealization
import AllThoseEPPA.Applications.KOrientations.ReconstructionCarrier

/-!
# Canonical reconstruction of a nonroot in the embedded source

A source nonroot x∈S is represented by a witnessed R_P tuple in the
root-only source A₁. Transport its label via the *actual* language
component of the embedding ι₁, and its tuple via the vertex map ι₁.
This gives a canonical nonroot pair in the reconstructed witness.

Importantly, the centre of the resulting pair is ι₁.lang(x), not x
unless the second-stage embedding happens to have identity language
component. The unordered support is exactly the image under ι₁ of
the full ambient B₀ root set of x, independently of the enumeration.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The source realization data for one nonroot x. It remembers a
label and an ordered tuple so the incidence symbols E_P can also be
transported later, but the reconstructed vertex retains no choices. -/
structure SourceNonrootPattern
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V) (x : V) where
  n : ℕ
  pattern : RootPattern G k n
  tuple : Fin n → RootsIn G k S
  center_eq : pattern.center = x
  realized :
    (auxiliaryRootStructure G k S).rel
      (AuxiliaryRel.root pattern) tuple

namespace SourceNonrootPattern

variable {V : Type u} [Fintype V] {W : Type v}
variable {G : Digraph V} {k : ℕ} {S : Set V} {x : V}

/-- Given a successor-closed rooted source S, every nonroot x∈S
has a source realization with the full complete root enumeration. -/
theorem exists_of_nonroot
    (hClosed : ∀ a b : V, a ∈ S → G.Reaches a b → b ∈ S)
    (hRooted : ∀ a : V, a ∈ S → (G.roots k a).Nonempty)
    (hx : x ∈ S) (hNonroot : ¬ G.IsRoot k x) :
    Nonempty (SourceNonrootPattern G k S x) := by
  obtain ⟨n, P, xs, hc, hRel⟩ :=
    auxiliarySource_realizes_nonroot
      G k S hClosed x hx hNonroot (hRooted x hx)
  exact ⟨⟨n, P, xs, hc, hRel⟩⟩

/-- Transport a realized source nonroot through the exact embedding
ι₁. The relation label is transported by ι₁.lang; the tuple points
are transported by ι₁.toFun. -/
def toCanonical
    (d : SourceNonrootPattern G k S x)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    CanonicalNonroot G k B := by
  have hRel :
      B.rel (AuxiliaryRel.root
        (RootPattern.transportAut ι.lang d.pattern))
        (ι.toFun ∘ d.tuple) := by
    have hm :=
      (ι.map_rel_iff (AuxiliaryRel.root d.pattern) d.tuple).2
        d.realized
    change B.rel (AuxiliaryRel.root
        (RootPattern.transportAut ι.lang d.pattern))
        (ι.toFun ∘ d.tuple) at hm
    exact hm
  exact CanonicalNonroot.ofRelation
    (RootPattern.transportAut ι.lang d.pattern)
    (ι.toFun ∘ d.tuple) hRel

@[simp] theorem toCanonical_center
    (d : SourceNonrootPattern G k S x)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    (d.toCanonical B ι).center = ι.lang.1 x := by
  change ι.lang.1 d.pattern.center = ι.lang.1 x
  exact congrArg (fun t : V => ι.lang.1 t) d.center_eq

/-- The source relation tuple enumerates *precisely* the ambient
roots of its centre, viewed in the distinguished root sort. -/
theorem tuple_range_eq_roots
    (d : SourceNonrootPattern G k S x) :
    Set.range d.tuple =
      {r : RootsIn G k S | r.val ∈ G.roots k x} := by
  have ht : ∀ i, (d.tuple i).val = d.pattern.tuple i :=
    ((auxiliaryRootStructure_root G k d.n S d.pattern d.tuple).mp
      d.realized).2
  ext r
  constructor
  · rintro ⟨i, rfl⟩
    change (d.tuple i).val ∈ G.roots k x
    have hMem : (d.tuple i).val ∈ G.roots k d.pattern.center := by
      rw [d.pattern.roots_eq]
      exact ⟨i, (ht i).symm⟩
    simpa only [d.center_eq] using hMem
  · intro hr
    change r.val ∈ G.roots k x at hr
    have hMem : r.val ∈ G.roots k d.pattern.center := by
      simpa only [d.center_eq] using hr
    rw [d.pattern.roots_eq] at hMem
    obtain ⟨i, hi⟩ := hMem
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact (ht i).trans hi

/-- The intrinsic support of the reconstructed source copy is
exactly the image of the complete template root set. -/
theorem toCanonical_support_eq
    (d : SourceNonrootPattern G k S x)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B) :
    (d.toCanonical B ι).support =
      ι.toFun '' {r : RootsIn G k S | r.val ∈ G.roots k x} := by
  change Set.range (ι.toFun ∘ d.tuple) =
    ι.toFun '' {r : RootsIn G k S | r.val ∈ G.roots k x}
  rw [Set.range_comp, d.tuple_range_eq_roots]

end SourceNonrootPattern
end AllThoseEPPA.Applications.KOrientations
