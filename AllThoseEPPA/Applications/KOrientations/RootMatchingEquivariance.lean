import AllThoseEPPA.Applications.KOrientations.RootMatchingEquiv
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdgeAction

/-!
# Equivariance of the canonical root matching eta

The natural action of a second-stage automorphism f on non-root
vertices is (x,W) ↦ (f.lang(x), f''W). Its root-coordinate bijection
eta must transport *coordinatewise* with this action, not merely
as an unlabelled bijection of the support sets.

The proof is intrinsic: it uses the already checked equivariance of
the relation RootMatches and its uniqueness, not representatives
of any quotient or a choice of root enumerations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

namespace RootMatches

variable {V : Type u} [Fintype V] {W : Type v}
variable {G : Digraph V} {k : ℕ}
variable {B : Structure (auxiliaryLanguage G k) W}

/-- The canonical matching equivalence really satisfies its defining
intrinsic root correspondence; this is its reusable elimination rule. -/
theorem canonicalEquiv_rel
    (S : Set V)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B)
    (r : G.roots k p.center) :
    RootMatches G k B p r.val (canonicalEquiv S ι hFaith p r).val := by
  unfold canonicalEquiv
  dsimp
  exact (Classical.choose_spec
    (existsUnique_support S ι hFaith p r)).1

/-- Transport a template root by the full graph-automorphism
language component of f. -/
def mappedRoot
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B)
    (r : G.roots k p.center) :
    G.roots k (CanonicalNonroot.map f p).center := by
  refine ⟨f.lang.1 r.val, ?_⟩
  change f.lang.1 r.val ∈ G.roots k (f.lang.1 p.center)
  rw [G.graphAut_roots_image k f.lang p.center]
  exact ⟨r.val, r.property, rfl⟩

@[simp] theorem mappedRoot_val
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B)
    (r : G.roots k p.center) :
    (mappedRoot f p r).val = f.lang.1 r.val := rfl

/-- **Canonical eta is equivariant.**
For the transformed non-root (f.lang(x),f''W), matching the transformed
template root produces exactly f of the original matched root. -/
theorem canonicalEquiv_equivariant
    (S : Set V)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B)
    (r : G.roots k p.center) :
    (canonicalEquiv S ι hFaith (CanonicalNonroot.map f p)
      (mappedRoot f p r)).val =
    f (canonicalEquiv S ι hFaith p r).val := by
  let z := canonicalEquiv S ι hFaith p r
  have hz : RootMatches G k B p r.val z.val :=
    canonicalEquiv_rel S ι hFaith p r
  have hMapped : RootMatches G k B (CanonicalNonroot.map f p)
      (f.lang.1 r.val) (f z.val) :=
    rootMatches_map G k B f p r.val z.val hz
  have hEta : RootMatches G k B (CanonicalNonroot.map f p)
      (f.lang.1 r.val)
      (canonicalEquiv S ι hFaith (CanonicalNonroot.map f p)
        (mappedRoot f p r)).val := by
    exact canonicalEquiv_rel S ι hFaith
      (CanonicalNonroot.map f p) (mappedRoot f p r)
  exact RootMatches.right_unique
    (CanonicalNonroot.map f p) S ι hFaith hEta hMapped

end RootMatches

end AllThoseEPPA.Applications.KOrientations
