import AllThoseEPPA.Applications.KOrientations.LocalCorrespondenceGraph
import AllThoseEPPA.Applications.KOrientations.ReconstructionSupportMonotone

/-!
# Closure and directed reachability of the moved-support domain

A local graph correspondence is defined on reconstructed vertices whose
entire intrinsic support is sent to the embedded source root sort by one
fixed auxiliary automorphism. Support antitonicity shows that this domain
is successor-closed, not merely an induced subgraph.

The four-case checked local graph correspondence therefore also
preserves all directed paths, including paths through intermediate
vertices not specified in advance. These are essential preliminary
facts for preserving the unary d-function on closed pieces.

No surjectivity onto a template closed piece, converse path lifting,
or d-language isomorphism is claimed here.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The local domain is closed under every reconstructed edge. -/
theorem isMovedSupport_of_reconstructed_edge
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {x y : ReconstructedCarrier G k B}
    (hx : IsMovedSupport G k S B ι f x)
    (hEdge : ReconstructedEdge G k B x y) :
    IsMovedSupport G k S B ι f y := by
  intro w hw
  exact hx w
    (faithful_reconstructedEdge_support_antitone
      G k S B ι hFaith hEdge hw)

/-- The moved-support domain is also closed under arbitrary directed
paths, equivalently under the reconstructed unary successor function. -/
theorem isMovedSupport_of_reconstructed_reaches
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {x y : ReconstructedCarrier G k B}
    (hx : IsMovedSupport G k S B ι f x)
    (hPath : (faithfulReconstructedDigraph G k S B ι hFaith).Reaches x y) :
    IsMovedSupport G k S B ι f y := by
  intro w hw
  exact hx w
    (faithful_reconstructed_reaches_support_antitone
      G k S B ι hFaith hPath hw)

/-- Starting at any locally moved vertex, every reconstructed path
stays in the moved-support domain and its image under the canonical
local correspondence is a directed path in the template. -/
theorem localCorrespondence_reaches_of_reconstructed_reaches
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    {x y : ReconstructedCarrier G k B}
    (hPath : (faithfulReconstructedDigraph G k S B ι hFaith).Reaches x y) :
    ∀ hx : IsMovedSupport G k S B ι f x,
      ∃ hy : IsMovedSupport G k S B ι f y,
        G.Reaches
          (localCorrespondence G k S B ι f ⟨x, hx⟩)
          (localCorrespondence G k S B ι f ⟨y, hy⟩) := by
  induction hPath with
  | refl x =>
      intro hx
      exact ⟨hx, G.reaches_refl _⟩
  | @step x y z hEdge hRest ih =>
      intro hx
      have hy : IsMovedSupport G k S B ι f y :=
        isMovedSupport_of_reconstructed_edge
          G k S B ι hFaith f hx hEdge
      obtain ⟨hz, hTail⟩ := ih hy
      refine ⟨hz, G.reaches_trans ?_ hTail⟩
      exact G.reaches_of_edge
        ((localCorrespondence_edge_iff
          G k S B ι f ⟨x, hx⟩ ⟨y, hy⟩).mp hEdge)

/-- In particular the choice-free local map preserves reachability
between any two vertices of its subtype domain. -/
theorem localCorrespondence_preserves_reaches
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (x y : LocalReconstructedCarrier G k S B ι f)
    (hPath : (faithfulReconstructedDigraph G k S B ι hFaith).Reaches
      x.val y.val) :
    G.Reaches (localCorrespondence G k S B ι f x)
      (localCorrespondence G k S B ι f y) := by
  obtain ⟨hy, hImage⟩ :=
    localCorrespondence_reaches_of_reconstructed_reaches
      G k S B ι hFaith f hPath x.property
  have hEq :
      (⟨y.val, hy⟩ : LocalReconstructedCarrier G k S B ι f) = y :=
    Subtype.ext rfl
  simpa only [hEq] using hImage

end AllThoseEPPA.Applications.KOrientations
