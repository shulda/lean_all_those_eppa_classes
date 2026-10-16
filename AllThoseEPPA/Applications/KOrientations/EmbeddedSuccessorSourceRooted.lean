import AllThoseEPPA.Applications.KOrientations.FirstStageInClass
import AllThoseEPPA.Applications.KOrientations.SuccessorFaithfulFunctions
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Exact first-stage embeddings preserve rooted successor-closed sources

The second-stage pattern-lifting theorem assumes the distinguished
source S is successor-closed and that every vertex of S reaches an
actual k-root of the ambient template B₀. These hypotheses must be
derived from the original rooted input A and the *exact* successor
embedding A₀ → B₀; they are not hypotheses on arbitrary S, nor on
the whole (possibly nonrooted) first-stage witness B₀.

An exact unary successor embedding makes its image successor-closed.
That closure then makes all outgoing neighbours of an embedded
vertex come from the old structure, so exact relation preservation
yields equality of outdegrees and root status.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- An exact first-stage embedding identifies the entire successor
value with the image of the original successor value. -/
theorem successorEmbedding_successors_image
    {U : Type u} {V : Type v}
    (A : Digraph U) (G : Digraph V)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (a : U) :
    Structure.imageSet ι.toFun (A.successors a) =
      G.successors (ι a) := by
  have hMap := ι.map_func SuccessorSymbol.successor ![a]
  have htup : (ι.toFun ∘ ![a]) = ![ι a] := by
    funext i
    fin_cases i
    rfl
  rw [htup] at hMap
  simpa [successorStructure_successors, successorAction_on_func] using hMap

/-- The exact old-vertex image is closed under every directed path
in B₀, not just under edges. -/
theorem successorEmbedding_image_successorClosed
    {U : Type u} {V : Type v}
    (A : Digraph U) (G : Digraph V)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    ∀ x y : V, x ∈ Set.range ι.toFun →
      G.Reaches x y → y ∈ Set.range ι.toFun := by
  intro x y hx hxy
  obtain ⟨a, rfl⟩ := hx
  have hEq := successorEmbedding_successors_image A G ι a
  have hy : y ∈ G.successors (ι a) := hxy
  rw [← hEq] at hy
  obtain ⟨b, _, hb⟩ := hy
  exact ⟨b, hb⟩

/-- The image of an exact first-stage embedding is a closed
substructure of the unary successor language. -/
theorem successorEmbedding_image_isClosed
    {U : Type u} {V : Type v}
    (A : Digraph U) (G : Digraph V)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    (successorStructure G).IsClosed (Set.range ι.toFun) := by
  apply (successorStructure_isClosed_iff G (Set.range ι.toFun)).2
  exact successorEmbedding_image_successorClosed A G ι

/-- An exact first-stage embedding preserves and reflects the
underlying directed-edge relation on old vertices. -/
theorem successorEmbedding_edge_iff
    {U : Type u} {V : Type v}
    (A : Digraph U) (G : Digraph V)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (a b : U) :
    G.edge (ι a) (ι b) ↔ A.edge a b := by
  have h := ι.map_rel_iff EdgeSymbol.edge ![a, b]
  have htup : (ι.toFun ∘ ![a, b]) = ![ι a, ι b] := by
    funext i
    fin_cases i <;> rfl
  rw [htup] at h
  change G.edge (ι a) (ι b) ↔ A.edge a b at h
  exact h

/-- Any path in the input graph is transported to a path in the
first-stage witness graph. -/
theorem successorEmbedding_reaches
    {U : Type u} {V : Type v}
    (A : Digraph U) (G : Digraph V)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    {a b : U} (h : A.Reaches a b) :
    G.Reaches (ι a) (ι b) := by
  have heq := successorEmbedding_successors_image A G ι a
  have hrange : ι b ∈
      Structure.imageSet ι.toFun (A.successors a) :=
    ⟨b, h, rfl⟩
  rw [heq] at hrange
  exact hrange

/-- The exact successor embedding induces a bijection between
the **entire** original and embedded outgoing neighbourhoods. -/
noncomputable def successorEmbedding_outNeighborsEquiv
    {U : Type u} {V : Type v}
    [Fintype U] [Fintype V]
    (A : Digraph U) (G : Digraph V)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (a : U) :
    A.outNeighbors a ≃ G.outNeighbors (ι a) := by
  classical
  let e : A.outNeighbors a → G.outNeighbors (ι a) :=
    fun b => ⟨ι b.val,
      (G.mem_outNeighbors (ι a) (ι b.val)).2
        ((successorEmbedding_edge_iff A G ι a b.val).2
          ((A.mem_outNeighbors a b.val).1 b.property))⟩
  have hInj : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply ι.injective
    exact congrArg Subtype.val hxy
  have hSurj : Function.Surjective e := by
    intro b
    have hEdge : G.edge (ι a) b.val :=
      (G.mem_outNeighbors (ι a) b.val).1 b.property
    obtain ⟨c, hc⟩ :=
      successorEmbedding_image_successorClosed A G ι
        (ι a) b.val ⟨a, rfl⟩ (G.reaches_of_edge hEdge)
    have hOrigEdge : A.edge a c := by
      apply (successorEmbedding_edge_iff A G ι a c).1
      simpa only [hc] using hEdge
    refine ⟨⟨c, (A.mem_outNeighbors a c).2 hOrigEdge⟩, ?_⟩
    apply Subtype.ext
    exact hc
  exact Equiv.ofBijective e ⟨hInj, hSurj⟩

/-- Hence every embedded original vertex has **exactly** the
same outdegree in B₀ as in A₀. -/
theorem successorEmbedding_outdegree_eq
    {U : Type u} {V : Type v}
    [Fintype U] [Fintype V]
    (A : Digraph U) (G : Digraph V)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (a : U) :
    (G.outNeighbors (ι a)).card = (A.outNeighbors a).card := by
  classical
  have h := Fintype.card_congr
    (successorEmbedding_outNeighborsEquiv A G ι a)
  simpa only [Fintype.card_coe] using h.symm

/-- The k-root predicate is absolute between the input graph and
its successor-closed first-stage copy. -/
theorem successorEmbedding_isRoot_iff
    {U : Type u} {V : Type v}
    [Fintype U] [Fintype V]
    (A : Digraph U) (G : Digraph V) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (a : U) :
    G.IsRoot k (ι a) ↔ A.IsRoot k a := by
  change (G.outNeighbors (ι a)).card < k ↔
    (A.outNeighbors a).card < k
  rw [successorEmbedding_outdegree_eq A G ι a]

/-- A rooted original input yields nonempty **ambient** reachable
root sets at every point of its embedded image, with no assumption
that every point of B₀ has a reachable root. -/
theorem successorEmbedding_image_rooted
    {U : Type u} {V : Type v}
    [Fintype U] [Fintype V]
    (A : Digraph U) (G : Digraph V) (k : ℕ)
    (hRooted : A.HasReachableRoots k)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    ∀ x : V, x ∈ Set.range ι.toFun →
      (G.roots k x).Nonempty := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨r, hRoot, hReach⟩ := hRooted a
  exact ⟨ι r,
    (successorEmbedding_isRoot_iff A G k ι r).2 hRoot,
    successorEmbedding_reaches A G ι hReach⟩

end AllThoseEPPA.Applications.KOrientations
