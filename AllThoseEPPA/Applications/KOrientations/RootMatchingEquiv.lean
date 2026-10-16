import AllThoseEPPA.Applications.KOrientations.RootMatchingRelation

/-!
# Canonical root equivalence for reconstructed non-roots

From faithful equal-support coordinate matching we get, without
selecting representatives of realized labelled tuples, a unique
bijection between the template vertex's entire reachable-root set
and the realized support in the second EPPA witness.

This is the map η_(x,W) from the corrected manuscript. Its explicit
inverse and both inverse laws are derived from the intrinsic relation,
not from an arbitrarily chosen tuple or quotient transversal.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

namespace RootMatches

variable {V : Type u} [Fintype V] {W : Type v}
variable {G : Digraph V} {k : ℕ}
variable {B : Structure (auxiliaryLanguage G k) W}

/-- Every template root has a unique realized partner in the
canonical support of the reconstructed vertex. -/
theorem existsUnique_support
    (S : Set V)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B)
    (r : G.roots k p.center) :
    ∃! w : p.support, RootMatches G k B p r.val w.val := by
  obtain ⟨w, h⟩ := exists_of_root p r.property
  refine ⟨⟨w, support_mem p h⟩, h, ?_⟩
  intro z hz
  apply Subtype.ext
  exact (right_unique p S ι hFaith
    (r := r.val) (w₁ := w) (w₂ := z.val) h hz).symm

/-- Conversely every element of the realized support has a
unique template-root partner. -/
theorem existsUnique_root
    (S : Set V)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B)
    (w : p.support) :
    ∃! r : G.roots k p.center, RootMatches G k B p r.val w.val := by
  obtain ⟨r, h⟩ := exists_of_support p w.property
  refine ⟨⟨r, root_mem p h⟩, h, ?_⟩
  intro z hz
  apply Subtype.ext
  exact (left_unique p S ι hFaith
    (r₁ := r) (r₂ := z.val) (w := w.val) h hz).symm

/-- The choice-free canonical matching η_(x,W), an actual equivalence
of the full reachable-root set of the template centre and the
support of the reconstructed non-root.

Its definition depends only on the pair (x,W), not on any ordered
root enumeration or representative of a relation realization. -/
noncomputable def canonicalEquiv
    (S : Set V)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (p : CanonicalNonroot G k B) :
    (G.roots k p.center) ≃ p.support := by
  classical
  have hTo (r : G.roots k p.center) :
      ∃! w : p.support, RootMatches G k B p r.val w.val :=
    existsUnique_support S ι hFaith p r
  have hFrom (w : p.support) :
      ∃! r : G.roots k p.center, RootMatches G k B p r.val w.val :=
    existsUnique_root S ι hFaith p w
  let forward : (G.roots k p.center) → p.support :=
    fun r => Classical.choose (hTo r)
  let backward : p.support → (G.roots k p.center) :=
    fun w => Classical.choose (hFrom w)
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_ }
  · intro r
    apply Subtype.ext
    have h₁ : RootMatches G k B p
        (backward (forward r)).val (forward r).val :=
      (Classical.choose_spec (hFrom (forward r))).1
    have h₂ : RootMatches G k B p
        r.val (forward r).val :=
      (Classical.choose_spec (hTo r)).1
    exact left_unique p S ι hFaith h₁ h₂
  · intro w
    apply Subtype.ext
    have h₁ : RootMatches G k B p
        (backward w).val (forward (backward w)).val :=
      (Classical.choose_spec (hTo (backward w))).1
    have h₂ : RootMatches G k B p
        (backward w).val w.val :=
      (Classical.choose_spec (hFrom w)).1
    exact right_unique p S ι hFaith h₁ h₂

end RootMatches
end AllThoseEPPA.Applications.KOrientations
