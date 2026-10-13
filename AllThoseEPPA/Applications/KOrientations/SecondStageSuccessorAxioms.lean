import AllThoseEPPA.Applications.KOrientations.SecondStageRootDigraph
import AllThoseEPPA.Applications.KOrientations.FaithfulLocalTransfer
import AllThoseEPPA.Automorphism
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Local successor-closure axioms in the faithful auxiliary B₁ witness

The unrestricted EPPA construction does not require its arbitrary
output B₁ to satisfy the root-only template's reachability axioms.
We recover the following by transporting singleton closures and
realized edges into the original root-only source:

* exact unary set-valued successor membership is preserved/reflected
  under the auxiliary embedding and under all B₁ automorphisms;
* every B₁ edge is contained in the source's unary successor function;
* every vertex lies in its own unary successor value;
* unary successor values are transitively closed.

These are the local facts needed before identifying actual
root supports and proving the final orientation's outdegree bound.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The second-stage group action fixes the unique unary
successor symbol, regardless of its action on the relations. -/
@[simp] theorem auxiliaryAction_on_successor
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) (g : G.graphAut) :
    (auxiliaryAction G k).onFunc g AuxiliaryFunc.successor =
      AuxiliaryFunc.successor := rfl

/-- Exact auxiliary embeddings preserve and reflect reachability of
root vertices, encoded by the unary set-valued function. -/
theorem auxiliary_embedding_successor_iff
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (a b : RootsIn G k S) :
    G.Reaches a.val b.val ↔
      ι b ∈ B.func AuxiliaryFunc.successor ![ι a] := by
  have hmap := ι.map_func AuxiliaryFunc.successor ![a]
  have htup : (ι.toFun ∘ ![a]) = ![ι a] := by
    funext i
    fin_cases i
    rfl
  rw [htup] at hmap
  have heq :
      Structure.imageSet ι.toFun
          ((auxiliaryRootStructure G k S).func
            AuxiliaryFunc.successor ![a]) =
        B.func AuxiliaryFunc.successor ![ι a] := by
    simpa only [auxiliaryAction_on_successor] using hmap
  constructor
  · intro hab
    have hb : b ∈ (auxiliaryRootStructure G k S).func
        AuxiliaryFunc.successor ![a] := hab
    rw [← heq]
    exact ⟨b, hb, rfl⟩
  · intro hb
    rw [← heq] at hb
    obtain ⟨c, hc, hcb⟩ := hb
    have he : c = b := ι.injective hcb
    simpa only [he] using hc

/-- Exact set-valued successor membership is transported both ways
by the full B₁ automorphism including its language component. -/
theorem auxiliary_automorphism_successor_iff
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (f : Structure.Automorphism (auxiliaryAction G k) B)
    (x y : W) :
    y ∈ B.func AuxiliaryFunc.successor ![x] ↔
      f y ∈ B.func AuxiliaryFunc.successor ![f x] := by
  have hmap := Structure.Automorphism.map_func
    f AuxiliaryFunc.successor ![x]
  have htup : (f ∘ ![x]) = ![f x] := by
    funext i
    fin_cases i
    rfl
  rw [htup] at hmap
  have heq :
      Structure.imageSet f (B.func AuxiliaryFunc.successor ![x]) =
        B.func AuxiliaryFunc.successor ![f x] := by
    simpa only [auxiliaryAction_on_successor] using hmap
  constructor
  · intro hy
    rw [← heq]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzEq : z = y := f.toEquiv.injective hzy
    simpa only [hzEq] using hz

/-- Any unary function value is contained in the closure of its
argument, even for a completely arbitrary auxiliary structure. -/
theorem auxiliary_successorValue_subset_closureAt
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ)
    (B : Structure (auxiliaryLanguage G k) W)
    (x : W) :
    B.func AuxiliaryFunc.successor ![x] ⊆
      B.closureAtSet x := by
  intro y hy
  apply (B.isClosed_closureSet {x})
    AuxiliaryFunc.successor ![x]
  · intro i
    fin_cases i
    exact B.mem_closureAtSet x
  · exact hy

/-- Every realized B₁ root-to-root graph edge lies inside the
unary successor-function value at its source. -/
theorem faithful_auxiliary_edge_mem_successors
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {x y : W} (hxy : B.rel AuxiliaryRel.edge ![x,y]) :
    y ∈ B.func AuxiliaryFunc.successor ![x] := by
  obtain ⟨f, zs, hpts, hSource⟩ :=
    faithful_auxiliary_relation_movable G k S B ι hFaith
      AuxiliaryRel.edge ![x,y] hxy
  have hab : G.edge (zs 0).val (zs 1).val := by
    change G.edge (zs 0).val (zs 1).val at hSource
    exact hSource
  have hReach : G.Reaches (zs 0).val (zs 1).val :=
    G.reaches_of_edge hab
  have himg : ι (zs 1) ∈
      B.func AuxiliaryFunc.successor ![ι (zs 0)] :=
    (auxiliary_embedding_successor_iff G k S B ι
      (zs 0) (zs 1)).mp hReach
  have hfxy : f y ∈ B.func AuxiliaryFunc.successor ![f x] := by
    simpa only [hpts (0 : Fin 2), hpts (1 : Fin 2)] using himg
  exact (auxiliary_automorphism_successor_iff G k B f x y).mpr hfxy

/-- Self-membership of unary successors transfers from the
root-only source through faithful singleton-closure transport. -/
theorem faithful_auxiliary_successor_self
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    (x : W) :
    x ∈ B.func AuxiliaryFunc.successor ![x] := by
  obtain ⟨f, hmove⟩ :=
    faithful_moves_vertexClosure (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B ι hFaith x
  obtain ⟨a, ha⟩ := hmove x (B.mem_closureAtSet x)
  have hReach : G.Reaches a.val a.val := G.reaches_refl a.val
  have haVal : ι a ∈ B.func AuxiliaryFunc.successor ![ι a] :=
    (auxiliary_embedding_successor_iff G k S B ι a a).mp hReach
  have hf : f x ∈ B.func AuxiliaryFunc.successor ![f x] := by
    simpa only [ha] using haVal
  exact (auxiliary_automorphism_successor_iff G k B f x x).mpr hf

/-- The B₁ unary function is transitively closed, although its
unrestricted construction made no such global demand. -/
theorem faithful_auxiliary_successor_trans
    {V : Type u} {W : Type v} [Fintype V]
    (G : Digraph V) (k : ℕ) (S : Set V)
    (B : Structure (auxiliaryLanguage G k) W)
    (ι : Structure.Embedding (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B)
    (hFaith : Structure.IsIrreducibleStructureFaithful
      (auxiliaryAction G k) ι)
    {x y z : W}
    (hxy : y ∈ B.func AuxiliaryFunc.successor ![x])
    (hyz : z ∈ B.func AuxiliaryFunc.successor ![y]) :
    z ∈ B.func AuxiliaryFunc.successor ![x] := by
  have hycl : y ∈ B.closureAtSet x :=
    auxiliary_successorValue_subset_closureAt G k B x hxy
  have hzcl : z ∈ B.closureAtSet x :=
    (B.closureAtSet_subset_of_mem hycl)
      (auxiliary_successorValue_subset_closureAt G k B y hyz)
  obtain ⟨f, hmove⟩ :=
    faithful_moves_vertexClosure (auxiliaryAction G k)
      (auxiliaryRootStructure G k S) B ι hFaith x
  obtain ⟨a, ha⟩ := hmove x (B.mem_closureAtSet x)
  obtain ⟨b, hb⟩ := hmove y hycl
  obtain ⟨c, hc⟩ := hmove z hzcl
  have hxyf : f y ∈ B.func AuxiliaryFunc.successor ![f x] :=
    (auxiliary_automorphism_successor_iff G k B f x y).mp hxy
  have hyzf : f z ∈ B.func AuxiliaryFunc.successor ![f y] :=
    (auxiliary_automorphism_successor_iff G k B f y z).mp hyz
  have hab : G.Reaches a.val b.val := by
    apply (auxiliary_embedding_successor_iff G k S B ι a b).mpr
    simpa only [ha, hb] using hxyf
  have hbc : G.Reaches b.val c.val := by
    apply (auxiliary_embedding_successor_iff G k S B ι b c).mpr
    simpa only [hb, hc] using hyzf
  have hac : G.Reaches a.val c.val :=
    G.reaches_trans hab hbc
  have hxzf : f z ∈ B.func AuxiliaryFunc.successor ![f x] := by
    have h := (auxiliary_embedding_successor_iff G k S B ι a c).mp hac
    simpa only [ha, hc] using h
  exact (auxiliary_automorphism_successor_iff G k B f x z).mpr hxzf

end AllThoseEPPA.Applications.KOrientations
