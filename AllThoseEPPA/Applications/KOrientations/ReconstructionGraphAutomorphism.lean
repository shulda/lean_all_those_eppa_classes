import AllThoseEPPA.Applications.KOrientations.ReconstructedDigraph
import AllThoseEPPA.Applications.KOrientations.ReconstructionEdgeAction
import AllThoseEPPA.Applications.KOrientations.GraphAutomorphismGroup

/-!
# The canonical B₁ action as actual reconstructed graph automorphisms

The previous proof showed that the vertex permutation associated
with every automorphism f of the second-stage witness B₁ preserves
and reflects all four edge clauses of the reconstructed graph.

Package this as an element of the **actual automorphism subgroup**
of the final oriented graph. Composition remains coordinatewise and
requires neither a choice of root-pattern representatives nor a lift
of the B₁ language component from a quotient group.

The result is graph-theoretic; the ultimate coherent extension in
the full d-language must additionally preserve its set-valued
successor and higher-arity root-fibre functions.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- A genuine second-stage automorphism induces an automorphism of
the entire reconstructed oriented graph, not just a permutation
of its underlying vertex set. -/
noncomputable def reconstructedGraphAutomorphism
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B) :
    (faithfulReconstructedDigraph G k S B ι hFaith).graphAut := by
  refine ⟨reconstructedVertexPerm G k B f, ?_⟩
  intro x y
  change ReconstructedEdge G k B
      (reconstructedVertexPerm G k B f x)
      (reconstructedVertexPerm G k B f y) ↔
      ReconstructedEdge G k B x y
  exact (reconstructedEdge_iff_map G k B f x y).symm

@[simp] theorem reconstructedGraphAutomorphism_apply
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (x : ReconstructedCarrier G k B) :
    (reconstructedGraphAutomorphism G k S B ι hFaith f).1 x =
      reconstructedVertexPerm G k B f x :=
  rfl

/-- Composition on reconstructed graph automorphisms agrees
exactly with composition of second-stage automorphisms. -/
theorem reconstructedGraphAutomorphism_comp
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (f g : Structure.Automorphism (auxiliaryAction G k) B) :
    reconstructedGraphAutomorphism G k S B ι hFaith (f.comp g) =
      reconstructedGraphAutomorphism G k S B ι hFaith f *
        reconstructedGraphAutomorphism G k S B ι hFaith g := by
  apply Subtype.ext
  change reconstructedVertexPerm G k B (f.comp g) =
      reconstructedVertexPerm G k B f *
      reconstructedVertexPerm G k B g
  exact reconstructedVertexPerm_comp G k B f g

end AllThoseEPPA.Applications.KOrientations
