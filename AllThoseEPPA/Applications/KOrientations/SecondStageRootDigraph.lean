import AllThoseEPPA.Applications.KOrientations.SecondStageRelationTransfer
import AllThoseEPPA.Applications.KOrientations.FaithfulLocalTransfer
import AllThoseEPPA.Automorphism
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The root-to-root edge reduct of the second-stage witness is oriented

The unrestricted coherent EPPA theorem supplies an arbitrary
auxiliary-language structure B₁. Its E relation is *not* assumed to
be oriented by the general theorem.

A realized B₁ edge has irreducible closure, which the faithful witness
moves into the root-only template. There the edge is one of the
original asymmetric oriented graph. Transporting a hypothetical
reverse edge by the *same* automorphism gives a contradiction.

This constructs an actual Digraph W. Remaining local graph/closure
axioms (e.g. successors contain edges) are independent obligations.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The binary auxiliary edge symbol is fixed by every element of
the entire (possibly nonfaithful) language action. -/
@[simp] theorem auxiliaryAction_on_edge
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (g : G.graphAut) :
    (auxiliaryAction G k).onRel g AuxiliaryRel.edge =
      AuxiliaryRel.edge := by
  rfl

/-- Irreducible-structure faithfulness forces B₁'s root-to-root
binary edge relation to be asymmetric, even though the unrestricted
EPPA construction does not impose this axiom. -/
theorem faithful_auxiliary_edge_asymm
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {x y : W} (hxy : B.rel AuxiliaryRel.edge ![x,y]) :
    ¬ B.rel AuxiliaryRel.edge ![y,x] := by
  intro hyx
  obtain ⟨f, zs, hpts, hSource⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      AuxiliaryRel.edge ![x,y] hxy
  have hab : G.edge (zs 0).val (zs 1).val := by
    change G.edge (zs 0).val (zs 1).val at hSource
    exact hSource
  have hrevB : B.rel AuxiliaryRel.edge (f ∘ ![y,x]) := by
    simpa only [auxiliaryAction_on_edge] using
      ((Structure.Automorphism.map_rel_iff
        f AuxiliaryRel.edge ![y,x]).2 hyx)
  have htup :
      (f ∘ ![y,x]) = (ι.toFun ∘ ![zs 1,zs 0]) := by
    funext i
    fin_cases i
    · simpa [Function.comp_def] using (hpts (1 : Fin 2))
    · simpa [Function.comp_def] using (hpts (0 : Fin 2))
  rw [htup] at hrevB
  have hba : G.edge (zs 1).val (zs 0).val := by
    have hsrc :
        (auxiliaryRootStructure G k S).rel
          AuxiliaryRel.edge ![zs 1, zs 0] := by
      apply (ι.map_rel_iff AuxiliaryRel.edge ![zs 1,zs 0]).1
      simpa only [auxiliaryAction_on_edge] using hrevB
    change G.edge (zs 1).val (zs 0).val at hsrc
    exact hsrc
  exact (G.asymmetric hab) hba

/-- The actual oriented edge graph on the root carrier W of B₁.
This is not yet the full reconstructed graph with non-root vertices. -/
def faithfulAuxiliaryRootDigraph
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι) :
    Digraph W where
  edge x y := B.rel AuxiliaryRel.edge ![x,y]
  asymmetric := by
    intro x y hxy
    exact faithful_auxiliary_edge_asymm G k S B ι hFaith hxy

end AllThoseEPPA.Applications.KOrientations
