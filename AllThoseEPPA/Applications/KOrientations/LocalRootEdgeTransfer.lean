import AllThoseEPPA.Applications.KOrientations.ReconstructionEdgeAction
import AllThoseEPPA.Automorphism
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Exact root-root edge transport under a common B₁ automorphism

This is the root/root case of the paper's local correspondence
property P2. When a single auxiliary automorphism f moves two B₁
vertices a,b to the distinguished source roots r,s, exact
preservation of the edge relation by f and by the source embedding
shows that a→b is equivalent to r→s. This result both preserves
and reflects the oriented binary relation.

Other cases involving reconstructed nonroots will use E_P or the
canonical root matching, rather than assuming them as definitions.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

theorem faithful_auxiliary_edge_iff_under_move
    {V : Type u} [Fintype V] {W : Type v}
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (a b : W) (r s : RootsIn G k S)
    (hr : f a = ι r) (hs : f b = ι s) :
    B.rel AuxiliaryRel.edge ![a,b] ↔
      G.edge r.val s.val := by
  have hMap := Structure.Automorphism.map_rel_iff
    f AuxiliaryRel.edge ![a,b]
  have hTuple : (f ∘ ![a,b]) = ![f a,f b] := by
    funext i
    fin_cases i <;> rfl
  rw [hTuple] at hMap
  have hF :
      B.rel AuxiliaryRel.edge ![a,b] ↔
        B.rel AuxiliaryRel.edge ![f a,f b] := by
    change
      B.rel AuxiliaryRel.edge ![f a,f b] ↔
        B.rel AuxiliaryRel.edge ![a,b] at hMap
    exact hMap.symm
  have hEmbed := ι.map_rel_iff
    AuxiliaryRel.edge ![r,s]
  have hEmbTuple : (ι.toFun ∘ ![r,s]) = ![ι r,ι s] := by
    funext i
    fin_cases i <;> rfl
  rw [hEmbTuple] at hEmbed
  have hA :
      B.rel AuxiliaryRel.edge ![ι r,ι s] ↔
        G.edge r.val s.val := by
    change B.rel AuxiliaryRel.edge ![ι r,ι s] ↔
      G.edge r.val s.val at hEmbed
    exact hEmbed
  calc
    B.rel AuxiliaryRel.edge ![a,b] ↔
        B.rel AuxiliaryRel.edge ![f a,f b] := hF
    _ ↔ B.rel AuxiliaryRel.edge ![ι r,ι s] := by
      rw [hr,hs]
    _ ↔ G.edge r.val s.val := hA

end AllThoseEPPA.Applications.KOrientations
