import AllThoseEPPA.Applications.KOrientations.ClosedGraphDTraceIso
import AllThoseEPPA.Applications.KOrientations.EmbeddedSuccessorSourceRooted

/-!
# Original full d-trace and exact successor-embedded source inside B₀

The first coherent EPPA stage embeds the old unary successor structure
A₀ into a larger successor witness B₀. Its image S is successor-closed
but need NOT be d-closed in the AMBIENT d-expansion of B₀:
higher-arity root-fibre functions may find new vertices outside S.

The correct second-stage source is the INTRINSIC restricted d-trace
on S. The already certified theorem closedGraph_dTraceEmbedding
says an exact graph isomorphism between successor-closed pieces
also transports every restricted higher-arity F_n fibre, WITHOUT
assuming either ambient piece d-closed.

Here the first-stage successor embedding gives a literal equivalence
of the old full vertex carrier with its embedded S-image. We apply
the above graph/d-trace theorem to show that ALL d-relations and
ALL arity-indexed set-valued function fibres agree exactly.
This is a real bijective public Structure.Embedding, not a mere
graph map and not a fake unary encoding of F_n.

The domain/range transport for arbitrary d-partial automorphisms
and the induced Γ-partial root automorphism will use this API next.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The first-stage EXACT successor embedding identifies the whole
original carrier V with the truly embedded old source S inside B₀.
The target is the ACTUAL dependent subtype of the image, not all B₀. -/
noncomputable def firstStageSourceSubtypeEquiv
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    (Set.univ : Set V) ≃ Set.range ι.toFun := by
  classical
  let f : (Set.univ : Set V) → Set.range ι.toFun :=
    fun x => ⟨ι x.val, ⟨x.val, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply ι.injective
    exact congrArg Subtype.val hxy
  · rintro ⟨w, hw⟩
    obtain ⟨x, hx⟩ := hw
    refine ⟨⟨x, Set.mem_univ x⟩, ?_⟩
    apply Subtype.ext
    exact hx

/-- The subtype equivalence transports a vertex precisely by
the original actual first-stage successor embedding. -/
@[simp] theorem firstStageSourceSubtypeEquiv_val
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G))
    (x : (Set.univ : Set V)) :
    (firstStageSourceSubtypeEquiv A G ι x).val = ι x.val :=
  rfl

/-- ACTUAL bijective full d-language embedding from the intrinsic
all-arity d-trace on the original source to the intrinsic all-arity
d-trace of the first witness's embedded source S. No hypothesis
that S is d-closed in ambient B₀: ONLY genuine successor-closedness
is used, which follows from the first-stage exact unary map_func. -/
noncomputable def firstStageSourceDTraceEmbedding
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    Structure.Embedding dTrivialAction
      (dTraceStructure A k (Set.univ : Set V))
      (dTraceStructure G k (Set.range ι.toFun)) := by
  let e := firstStageSourceSubtypeEquiv A G ι
  have hS : ∀ (x y : V), x ∈ (Set.univ : Set V) →
      A.edge x y → y ∈ (Set.univ : Set V) := by
    intro x y _ _
    trivial
  have hT : ∀ (x y : W), x ∈ Set.range ι.toFun →
      G.edge x y → y ∈ Set.range ι.toFun := by
    intro x y hx hxy
    exact successorEmbedding_image_successorClosed A G ι
      x y hx (G.reaches_of_edge hxy)
  have hEdge : ∀ x y : (Set.univ : Set V),
      A.edge x.val y.val ↔
        G.edge (e x).val (e y).val := by
    intro x y
    change A.edge x.val y.val ↔
      G.edge (ι x.val) (ι y.val)
    exact (successorEmbedding_edge_iff A G ι x.val y.val).symm
  exact closedGraph_dTraceEmbedding A G k
    (Set.univ : Set V) (Set.range ι.toFun) hS hT e hEdge

/-- The first-stage induced full d-trace map covers ALL original
source-supported vertices; it is not just an embedding into a
proper image with unknown surjectivity. -/
theorem firstStageSourceDTraceEmbedding_bijective
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    Function.Bijective
      (firstStageSourceDTraceEmbedding A G k ι).toFun := by
  exact (firstStageSourceSubtypeEquiv A G ι).bijective

end AllThoseEPPA.Applications.KOrientations
