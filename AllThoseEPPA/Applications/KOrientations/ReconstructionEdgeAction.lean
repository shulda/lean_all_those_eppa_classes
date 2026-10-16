import AllThoseEPPA.Applications.KOrientations.ReconstructionEdges
import AllThoseEPPA.Applications.KOrientations.ReconstructionVertexAction
import AllThoseEPPA.Automorphism
import Mathlib.Tactic.FinCases

/-!
# Equivariance of the four reconstructed edge clauses

A B₁ automorphism already has the actual graph automorphism of B₀ as
its language component. It acts on the choice-free carrier by
(a ↦ f(a)) on root vertices and (x,W) ↦ (f.lang(x), f''W)
on non-roots.

This file shows that this permutation preserves AND reflects the
four-case reconstructed edge relation. The result will become the
graph part of the final automorphism-gluing theorem. We do not
presuppose that the graph itself is already a k-orientation.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- An intrinsic root-coordinate match is equivariant under the
full second-stage automorphism, including its language component. -/
theorem rootMatches_map
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (p : CanonicalNonroot G k B) (r : V) (w : W)
    (h : RootMatches G k B p r w) :
    RootMatches G k B (CanonicalNonroot.map f p)
      (f.lang.1 r) (f w) := by
  obtain ⟨n, P, xs, i, hc, hR, hU, hr, hw⟩ := h
  refine ⟨n, RootPattern.transportAut f.lang P,
    f ∘ xs, i, ?_, ?_, ?_, ?_, ?_⟩
  · change f.lang.1 P.center = f.lang.1 p.center
    exact congrArg (f.lang.1) hc
  · change B.rel
      ((auxiliaryAction G k).onRel f.lang (AuxiliaryRel.root P))
      (f ∘ xs)
    exact (Structure.Automorphism.map_rel_iff
      f (AuxiliaryRel.root P) xs).2 hR
  · change Set.range (f ∘ xs) = f '' p.support
    rw [Set.range_comp, hU]
  · change f.lang.1 (P.tuple i) = f.lang.1 r
    exact congrArg (f.lang.1) hr
  · change f (xs i) = f w
    exact congrArg f hw

/-- The existential E_P incidence test on (a,(x,W)) is
equivariant, without choosing any representative of the support. -/
theorem incomingRealized_map
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (a : W) (p : CanonicalNonroot G k B)
    (h : IncomingRealized G k B a p) :
    IncomingRealized G k B (f a) (CanonicalNonroot.map f p) := by
  obtain ⟨n, P, ys, hc, hE, ha, hU⟩ := h
  refine ⟨n, RootPattern.transportAut f.lang P,
    f ∘ ys, ?_, ?_, ?_, ?_⟩
  · change f.lang.1 P.center = f.lang.1 p.center
    exact congrArg (f.lang.1) hc
  · change B.rel
      ((auxiliaryAction G k).onRel f.lang (AuxiliaryRel.incoming P))
      (f ∘ ys)
    exact (Structure.Automorphism.map_rel_iff
      f (AuxiliaryRel.incoming P) ys).2 hE
  · change f (ys 0) = f a
    exact congrArg f ha
  · change Set.range
      (fun i : Fin n => f (ys (Fin.succ i))) = f '' p.support
    calc
      Set.range (fun i : Fin n => f (ys (Fin.succ i))) =
          f '' Set.range (fun i : Fin n => ys (Fin.succ i)) := by
        change Set.range (f ∘ (fun i : Fin n => ys (Fin.succ i))) = _
        rw [Set.range_comp]
      _ = f '' p.support :=
        congrArg (fun T : Set W => f '' T) hU

/-- Every one of the four reconstructed edge clauses is preserved
by the coordinatewise vertex permutation of a B₁ automorphism. -/
theorem reconstructedEdge_map
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {x y : ReconstructedCarrier G k B}
    (h : ReconstructedEdge G k B x y) :
    ReconstructedEdge G k B
      (reconstructedVertexPerm G k B f x)
      (reconstructedVertexPerm G k B f y) := by
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          change B.rel AuxiliaryRel.edge ![f a, f b]
          have hmap :=
            (Structure.Automorphism.map_rel_iff
              f AuxiliaryRel.edge ![a, b]).2 h
          have htup : (f ∘ ![a, b]) = ![f a, f b] := by
            funext i
            fin_cases i <;> rfl
          rw [htup] at hmap
          change B.rel AuxiliaryRel.edge ![f a, f b] at hmap
          exact hmap
      | inr p =>
          change IncomingRealized G k B (f a)
            (CanonicalNonroot.map f p)
          exact incomingRealized_map G k B f a p h
  | inr p =>
      cases y with
      | inl b =>
          change ∃ r : V,
            G.edge (f.lang.1 p.center) r ∧
            RootMatches G k B
              (CanonicalNonroot.map f p) r (f b)
          obtain ⟨r, he, hm⟩ := h
          refine ⟨f.lang.1 r, ?_, ?_⟩
          · exact (f.lang.2 p.center r).2 he
          · exact rootMatches_map G k B f p r b hm
      | inr q =>
          change
            G.edge (f.lang.1 p.center) (f.lang.1 q.center) ∧
              (f '' q.support) ⊆ (f '' p.support)
          exact ⟨(f.lang.2 p.center q.center).2 h.1,
            Set.image_mono h.2⟩

/-- Every reconstructed edge is preserved and reflected by the
vertex permutation. This has no hypothesis of graph asymmetry,
outdegree bounds or nonempty roots: it follows directly from the
four intrinsic clauses and their equivariance. -/
theorem reconstructedEdge_iff_map
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (x y : ReconstructedCarrier G k B) :
    ReconstructedEdge G k B x y ↔
      ReconstructedEdge G k B
        (reconstructedVertexPerm G k B f x)
        (reconstructedVertexPerm G k B f y) := by
  constructor
  · exact reconstructedEdge_map G k B f
  · intro h
    have h' := reconstructedEdge_map G k B f.symm h
    have hinv (z : ReconstructedCarrier G k B) :
        reconstructedVertexPerm G k B f.symm
          (reconstructedVertexPerm G k B f z) = z := by
      cases z with
      | inl w =>
          change Sum.inl (f.symm (f w)) = Sum.inl w
          rw [Structure.Automorphism.symm_apply_apply]
      | inr p =>
          change Sum.inr
            (CanonicalNonroot.map f.symm (CanonicalNonroot.map f p)) =
              Sum.inr p
          rw [CanonicalNonroot.map_symm_apply]
    rw [hinv x, hinv y] at h'
    exact h'

end AllThoseEPPA.Applications.KOrientations
