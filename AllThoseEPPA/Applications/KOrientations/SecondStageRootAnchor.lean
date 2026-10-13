import AllThoseEPPA.Applications.KOrientations.SecondStageSuccessorAxioms
import AllThoseEPPA.Applications.KOrientations.SecondStageRootDigraph
import AllThoseEPPA.Applications.KOrientations.FaithfulLocalTransfer
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# One common faithful move for all neighbours of a B₁-root

To bound the total reconstructed outdegree of a vertex a in B₁,
one must move its *entire singleton closure*, not independently
move different edges. An auxiliary root anchor packages the moving
automorphism, its source root, and the transport of every point
in that closure into the original root sort.

A first consequence is the exact transport of each root-to-root
outgoing edge along this common automorphism. The root-to-nonroot
neighbours will subsequently use the same anchor, ensuring that
the complete neighbourhood can be counted in B₀.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

structure AuxiliaryRootAnchor
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (a : W) where
  mover : Structure.Automorphism (auxiliaryAction G k) B
  source : RootsIn G k S
  source_eq : mover a = ι source
  moves_closure :
    ∀ y ∈ B.closureAtSet a,
      ∃ b : RootsIn G k S, mover y = ι b

/-- Irreducible-structure faithfulness supplies a common root anchor
for the entire one-point closure, uniformly over all its neighbours. -/
theorem auxiliaryRootAnchor_exists
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (a : W) :
    Nonempty (AuxiliaryRootAnchor G k S B ι a) := by
  obtain ⟨f, hf⟩ :=
    faithful_moves_vertexClosure (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B ι hFaith a
  obtain ⟨r, hr⟩ := hf a (B.mem_closureAtSet a)
  exact ⟨⟨f, r, hr, hf⟩⟩

namespace AuxiliaryRootAnchor

variable {V : Type u} [Fintype V] {W : Type v}
variable {G : Digraph V} {k : ℕ} {S : Set V}
variable {B : Structure (auxiliaryLanguage G k) W}
variable {ι : Structure.Embedding (auxiliaryAction G k)
    (auxiliaryRootStructure G k S) B}
variable {a : W}

/-- All root-to-root outgoing neighbours are seen inside the original
source root sort under one common faithful automorphism. -/
theorem move_rootEdge
    (anchor : AuxiliaryRootAnchor G k S B ι a)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {b : W} (hEdge : B.rel AuxiliaryRel.edge ![a,b]) :
    ∃ t : RootsIn G k S,
      anchor.mover b = ι t ∧ G.edge anchor.source.val t.val := by
  have hbF : b ∈ B.func AuxiliaryFunc.successor ![a] :=
    faithful_auxiliary_edge_mem_successors G k S B ι hFaith hEdge
  have hbClosed : b ∈ B.closureAtSet a :=
    auxiliary_successorValue_subset_closureAt G k B a hbF
  obtain ⟨t, ht⟩ := anchor.moves_closure b hbClosed
  have hB :
      B.rel AuxiliaryRel.edge
        (anchor.mover ∘ ![a,b]) := by
    simpa only [auxiliaryAction_on_edge] using
      ((Structure.Automorphism.map_rel_iff
        anchor.mover AuxiliaryRel.edge ![a,b]).2 hEdge)
  have hTuple :
      (anchor.mover ∘ ![a,b]) =
      (ι.toFun ∘ ![anchor.source,t]) := by
    funext i
    fin_cases i
    · simpa only [Function.comp_def] using anchor.source_eq
    · simpa only [Function.comp_def] using ht
  rw [hTuple] at hB
  have hSrc : (auxiliaryRootStructure G k S).rel
      AuxiliaryRel.edge ![anchor.source,t] := by
    apply (ι.map_rel_iff AuxiliaryRel.edge ![anchor.source,t]).1
    simpa only [auxiliaryAction_on_edge] using hB
  exact ⟨t, ht, hSrc⟩

/-- Distinct root-to-root neighbours cannot collapse under the
common source move. This is a piece of the total root outdegree
injection, before adding non-root targets. -/
theorem rootEdge_target_injective
    (anchor : AuxiliaryRootAnchor G k S B ι a)
    {b c : W} {t : RootsIn G k S}
    (hb : anchor.mover b = ι t)
    (hc : anchor.mover c = ι t) :
    b = c := by
  apply anchor.mover.toEquiv.injective
  exact hb.trans hc.symm

end AuxiliaryRootAnchor
end AllThoseEPPA.Applications.KOrientations
