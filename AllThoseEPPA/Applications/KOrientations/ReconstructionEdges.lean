import AllThoseEPPA.Applications.KOrientations.RootMatchingEquiv
import AllThoseEPPA.Applications.KOrientations.SecondStageIncidence
import Mathlib.Data.Fin.VecNotation

/-!
# The four intrinsic edge clauses of the reconstructed graph

This module defines the binary relation on the *actual* finite carrier
of the final d-closure application. Non-roots are canonical pairs (x,W),
not quotient representatives.

The incoming E_P clause is existential: no unproved independence from
the chosen R_P-realization is needed merely to define the relation.
For nonroot-to-root edges, the intrinsic RootMatches relation is used
instead of arbitrary enumerations. The remaining cases are direct.

These definitions are an intermediate graph relation; proving that
they form a genuine finite k-orientation, that the d-functions are
canonical, and the final EPPA property are subsequent obligations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- Intrinsic root-to-nonroot incidence. The leading coordinate is a,
and the trailing coordinates enumerate *exactly* the support W.
All choices of labelled tuples are hidden inside the existential. -/
def IncomingRealized
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (a : W) (p : CanonicalNonroot G k B) : Prop :=
  ∃ (n : ℕ) (P : RootPattern G k n)
    (ys : Fin (n + 1) → W),
    P.center = p.center ∧
      B.rel (AuxiliaryRel.incoming P) ys ∧
      ys 0 = a ∧
      Set.range (fun i : Fin n => ys (Fin.succ i)) = p.support

/-- The intended reconstructed directed-edge relation. Its four cases
are root-root, root-nonroot, nonroot-root and nonroot-nonroot. -/
def ReconstructedEdge
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W) :
    ReconstructedCarrier G k B →
      ReconstructedCarrier G k B → Prop
  | .inl a, .inl b =>
      B.rel AuxiliaryRel.edge ![a, b]
  | .inl a, .inr p =>
      IncomingRealized G k B a p
  | .inr p, .inl a =>
      ∃ r : V, G.edge p.center r ∧ RootMatches G k B p r a
  | .inr p, .inr q =>
      G.edge p.center q.center ∧ q.support ⊆ p.support

@[simp] theorem reconstructedEdge_root_root
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (a b : W) :
    ReconstructedEdge G k B (.inl a) (.inl b) ↔
      B.rel AuxiliaryRel.edge ![a, b] :=
  Iff.rfl

@[simp] theorem reconstructedEdge_root_nonroot
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (a : W) (p : CanonicalNonroot G k B) :
    ReconstructedEdge G k B (.inl a) (.inr p) ↔
      IncomingRealized G k B a p :=
  Iff.rfl

@[simp] theorem reconstructedEdge_nonroot_root
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (p : CanonicalNonroot G k B) (a : W) :
    ReconstructedEdge G k B (.inr p) (.inl a) ↔
      ∃ r : V, G.edge p.center r ∧ RootMatches G k B p r a :=
  Iff.rfl

@[simp] theorem reconstructedEdge_nonroot_nonroot
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (p q : CanonicalNonroot G k B) :
    ReconstructedEdge G k B (.inr p) (.inr q) ↔
      G.edge p.center q.center ∧ q.support ⊆ p.support :=
  Iff.rfl

/-- Edges between non-roots are automatically asymmetric, using
only the asymmetry of the original template graph. -/
theorem reconstructedEdge_nonroot_asymm
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (p q : CanonicalNonroot G k B)
    (h : ReconstructedEdge G k B (.inr p) (.inr q)) :
    ¬ ReconstructedEdge G k B (.inr q) (.inr p) := by
  intro h'
  exact (G.asymmetric h.1) h'.1

/-- There are no loops in the nonroot-to-nonroot case, even before
all four edge clauses have been shown to be compatible. -/
theorem reconstructedEdge_nonroot_irrefl
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (p : CanonicalNonroot G k B) :
    ¬ ReconstructedEdge G k B (.inr p) (.inr p) := by
  intro h
  exact G.edge_irrefl p.center h.1

/-- A non-root to root edge necessarily points to one of the
non-root's realized support vertices. -/
theorem reconstructedEdge_nonroot_root_mem_support
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (p : CanonicalNonroot G k B) (a : W)
    (h : ReconstructedEdge G k B (.inr p) (.inl a)) :
    a ∈ p.support := by
  obtain ⟨r, _, hmatch⟩ := h
  exact RootMatches.support_mem p hmatch

/-- The support inclusion for a nonroot-to-nonroot edge is
literally part of the intrinsic construction. -/
theorem reconstructedEdge_nonroot_nonroot_support
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (p q : CanonicalNonroot G k B)
    (h : ReconstructedEdge G k B (.inr p) (.inr q)) :
    q.support ⊆ p.support := h.2

/-- In a faithful second-stage witness, every incoming E_P
realization indeed possesses its underlying root-only R_P tuple.
This makes the existential edge clause compatible with the
canonical nonroot support. -/
theorem incomingRealized_implies_rootRelation
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : W) (p : CanonicalNonroot G k B)
    (h : IncomingRealized G k B a p) :
    ∃ (n : ℕ) (P : RootPattern G k n) (xs : Fin n → W),
      P.center = p.center ∧
      B.rel (AuxiliaryRel.root P) xs ∧
      Set.range xs = p.support := by
  obtain ⟨n, P, ys, hc, hE, _, hU⟩ := h
  refine ⟨n, P, (fun i : Fin n => ys (Fin.succ i)), hc, ?_, hU⟩
  exact faithful_auxiliary_incoming_implies_root
    G k S B ι hFaith P ys hE

end AllThoseEPPA.Applications.KOrientations
