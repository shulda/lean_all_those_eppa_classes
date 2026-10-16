import AllThoseEPPA.Applications.KOrientations.SecondStageMatching
import AllThoseEPPA.Applications.KOrientations.ReconstructionCarrier

/-!
# Intrinsic root correspondence for canonical reconstructed non-roots

The relation `RootMatches G k B p r w` says that r is a template
root of the projection p.center and w its realized coordinate in
the auxiliary witness B.  Existentially quantifying over labels and
enumerations avoids selecting a representative of a quotient.

The checked equal-support matching lemma establishes right and left
uniqueness in this relation; existence is read from any witness of
realization of the canonical pair p.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A template root r corresponds to a realized root w in a
canonical non-root p=(x,W); both indices and enumerations are hidden
existentially. -/
def RootMatches {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (p : CanonicalNonroot G k B) (r : V) (w : W) : Prop :=
  ∃ (n : ℕ) (P : RootPattern G k n) (xs : Fin n → W) (i : Fin n),
    P.center = p.center ∧
    B.rel (AuxiliaryRel.root P) xs ∧
    Set.range xs = p.support ∧
    P.tuple i = r ∧ xs i = w

namespace RootMatches

variable {V : Type u} [Fintype V] {W : Type v}
variable {G : Digraph V} {k : ℕ}
variable {B : Structure (auxiliaryLanguage G k) W}
variable (p : CanonicalNonroot G k B)

/-- The template coordinate in a root matching is genuinely reachable
from the projection as a root. -/
theorem root_mem {r : V} {w : W}
    (h : RootMatches G k B p r w) :
    r ∈ G.roots k p.center := by
  obtain ⟨n, P, xs, i, hc, _, _, hr, _⟩ := h
  have hP : r ∈ G.roots k P.center := by
    rw [P.roots_eq]
    exact ⟨i, hr⟩
  simpa only [hc] using hP

/-- The realized matching coordinate belongs to the intrinsic
unordered support. -/
theorem support_mem {r : V} {w : W}
    (h : RootMatches G k B p r w) :
    w ∈ p.support := by
  obtain ⟨n, P, xs, i, _, _, hU, _, hw⟩ := h
  have h : w ∈ Set.range xs := ⟨i, hw⟩
  simpa only [hU] using h

/-- Every root of a reconstructed non-root has some partner in its
realized support. -/
theorem exists_of_root {r : V}
    (hr : r ∈ G.roots k p.center) :
    ∃ w : W, RootMatches G k B p r w := by
  obtain ⟨n, P, xs, hc, hRel, hU⟩ := p.witnessed
  have hP : r ∈ G.roots k P.center := by
    simpa only [hc] using hr
  rw [P.roots_eq] at hP
  obtain ⟨i, hi⟩ := hP
  exact ⟨xs i, n, P, xs, i, hc, hRel, hU, hi, rfl⟩

/-- Every element of the realized support has some template root
partner. -/
theorem exists_of_support {w : W}
    (hw : w ∈ p.support) :
    ∃ r : V, RootMatches G k B p r w := by
  obtain ⟨n, P, xs, hc, hRel, hU⟩ := p.witnessed
  have hRange : w ∈ Set.range xs := by
    rw [hU]
    exact hw
  obtain ⟨i, hi⟩ := hRange
  exact ⟨P.tuple i, n, P, xs, i, hc, hRel, hU, rfl, hi⟩

/-- There cannot be two realized coordinates for the same template
root, even when their witnessing labels use different enumerations. -/
theorem right_unique
    (S : Set V)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {r : V} {w₁ w₂ : W}
    (h₁ : RootMatches G k B p r w₁)
    (h₂ : RootMatches G k B p r w₂) : w₁ = w₂ := by
  obtain ⟨n, P, xs, i, _, hP, hU, hr₁, hw₁⟩ := h₁
  obtain ⟨m, Q, ys, j, _, hQ, hZ, hr₂, hw₂⟩ := h₂
  have hRange : Set.range xs = Set.range ys := hU.trans hZ.symm
  have hTemplate : P.tuple i = Q.tuple j := hr₁.trans hr₂.symm
  have hCoord :=
    (faithful_auxiliary_sameSupport_coordinateEq
      G k S B ι hFaith P Q xs ys hP hQ hRange i j).mp hTemplate
  exact hw₁.symm.trans (hCoord.trans hw₂)

/-- Distinct template roots cannot be identified by the same
realized root coordinate. -/
theorem left_unique
    (S : Set V)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {r₁ r₂ : V} {w : W}
    (h₁ : RootMatches G k B p r₁ w)
    (h₂ : RootMatches G k B p r₂ w) : r₁ = r₂ := by
  obtain ⟨n, P, xs, i, _, hP, hU, hr₁, hw₁⟩ := h₁
  obtain ⟨m, Q, ys, j, _, hQ, hZ, hr₂, hw₂⟩ := h₂
  have hRange : Set.range xs = Set.range ys := hU.trans hZ.symm
  have hCoord : xs i = ys j := hw₁.trans hw₂.symm
  have hTemplate :=
    (faithful_auxiliary_sameSupport_coordinateEq
      G k S B ι hFaith P Q xs ys hP hQ hRange i j).mpr hCoord
  exact hr₁.symm.trans (hTemplate.trans hr₂)

end RootMatches
end AllThoseEPPA.Applications.KOrientations
