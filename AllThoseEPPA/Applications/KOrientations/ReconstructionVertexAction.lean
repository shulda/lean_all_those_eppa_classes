import AllThoseEPPA.Applications.KOrientations.ReconstructionCarrier
import AllThoseEPPA.Automorphism
import Mathlib.Data.Set.Image

/-!
# Canonical, choice-free vertex action induced by a B₁ automorphism

The acting group on auxiliary relation symbols is the **actual** graph
automorphism group of B₀.  Thus the language component of any
automorphism f of the second witness *already determines* the map on
the template centre: no lift from a quotient is necessary.

This module proves that the intrinsic carrier pairs (x,W) are sent to
(f.lang(x), f''W), with inverses and correct composition.  These are
permutations of the future reconstructed graph's vertex set; graph
edge preservation is an independent, later obligation.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

namespace CanonicalNonroot

variable {V : Type u} [Fintype V] {W : Type v}
variable {G : Digraph V} {k : ℕ}
variable {B : Structure (auxiliaryLanguage G k) W}

/-- Transport the canonical non-root pair by the B₁ automorphism
and its **actual B₀ automorphism** language component. -/
def map
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B) : CanonicalNonroot G k B where
  center := f.lang.1 p.center
  support := f '' p.support
  witnessed := by
    obtain ⟨n, P, xs, hc, hRel, hU⟩ := p.witnessed
    refine ⟨n, RootPattern.transportAut f.lang P, f ∘ xs,
      ?_, ?_, ?_⟩
    · change f.lang.1 P.center = f.lang.1 p.center
      exact congrArg (f.lang.1) hc
    · change B.rel
        ((auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P))
        (f ∘ xs)
      exact (Structure.Automorphism.map_rel_iff f
        (AuxiliaryRel.root P) xs).2 hRel
    · rw [Set.range_comp, hU]

@[simp] theorem map_center
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B) :
    (map f p).center = f.lang.1 p.center := rfl

@[simp] theorem map_support
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B) :
    (map f p).support = f '' p.support := rfl

/-- The coordinatewise action respects the order of composition,
with no choice of label representatives. -/
theorem map_comp
    (f g : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B) :
    map (f.comp g) p = map f (map g p) := by
  apply eq_of_center_support
  · change (f.comp g).lang.1 p.center =
        f.lang.1 (g.lang.1 p.center)
    rw [Structure.Automorphism.comp_lang]
    change (f.lang * g.lang : G.graphAut).1 p.center =
      f.lang.1 (g.lang.1 p.center)
    simp
  · change (f.comp g) '' p.support =
        f '' (g '' p.support)
    ext z
    constructor
    · rintro ⟨x, hx, hxz⟩
      refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
      simpa only [Structure.Automorphism.comp_apply] using hxz
    · rintro ⟨y, ⟨x, hx, rfl⟩, hyz⟩
      refine ⟨x, hx, ?_⟩
      simpa only [Structure.Automorphism.comp_apply] using hyz

/-- Applying the inverse B₁ automorphism undoes the pair map. -/
theorem map_symm_apply
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B) :
    map f.symm (map f p) = p := by
  apply eq_of_center_support
  · change f.symm.lang.1 (f.lang.1 p.center) = p.center
    rw [Structure.Automorphism.symm_lang]
    exact (f.lang.1).symm_apply_apply p.center
  · change f.symm '' (f '' p.support) = p.support
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      simpa only [Structure.Automorphism.symm_apply_apply] using hx
    · intro hz
      exact ⟨f z, ⟨z, hz, rfl⟩,
        Structure.Automorphism.symm_apply_apply f z⟩

/-- The reverse inverse identity, using the full (not just
one-sided) permutation of the B₁ vertex sort. -/
theorem map_apply_symm
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B) :
    map f (map f.symm p) = p := by
  apply eq_of_center_support
  · change f.lang.1 (f.symm.lang.1 p.center) = p.center
    rw [Structure.Automorphism.symm_lang]
    exact (f.lang.1).apply_symm_apply p.center
  · change f '' (f.symm '' p.support) = p.support
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      simpa only [Structure.Automorphism.apply_symm_apply] using hx
    · intro hz
      exact ⟨f.symm z, ⟨z, hz, rfl⟩,
        Structure.Automorphism.apply_symm_apply f z⟩

end CanonicalNonroot

/-- The induced **actual permutation** of the tagged canonical
carrier.  The two sorts remain disjoint. -/
noncomputable def reconstructedVertexPerm
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    Equiv.Perm (ReconstructedCarrier G k B) where
  toFun := fun z => match z with
    | .inl w => .inl (f w)
    | .inr p => .inr (CanonicalNonroot.map f p)
  invFun := fun z => match z with
    | .inl w => .inl (f.symm w)
    | .inr p => .inr (CanonicalNonroot.map f.symm p)
  left_inv := by
    intro z
    cases z with
    | inl w =>
        change Sum.inl (f.symm (f w)) = Sum.inl w
        rw [Structure.Automorphism.symm_apply_apply]
    | inr p =>
        change Sum.inr
          (CanonicalNonroot.map f.symm (CanonicalNonroot.map f p)) =
            Sum.inr p
        rw [CanonicalNonroot.map_symm_apply]
  right_inv := by
    intro z
    cases z with
    | inl w =>
        change Sum.inl (f (f.symm w)) = Sum.inl w
        rw [Structure.Automorphism.apply_symm_apply]
    | inr p =>
        change Sum.inr
          (CanonicalNonroot.map f (CanonicalNonroot.map f.symm p)) =
            Sum.inr p
        rw [CanonicalNonroot.map_apply_symm]

/-- The vertex permutations are functorial for composition of
second-stage automorphisms.  This is the algebraic foundation for the
eventual coherence proof, separate from graph edge preservation. -/
theorem reconstructedVertexPerm_comp
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (f g : Structure.Automorphism (auxiliaryAction G k) B) :
    reconstructedVertexPerm G k B (f.comp g) =
      reconstructedVertexPerm G k B f *
        reconstructedVertexPerm G k B g := by
  ext z
  cases z with
  | inl w =>
      change Sum.inl ((f.comp g) w) = Sum.inl (f (g w))
      rw [Structure.Automorphism.comp_apply]
  | inr p =>
      change Sum.inr (CanonicalNonroot.map (f.comp g) p) =
        Sum.inr (CanonicalNonroot.map f (CanonicalNonroot.map g p))
      rw [CanonicalNonroot.map_comp]

end AllThoseEPPA.Applications.KOrientations
