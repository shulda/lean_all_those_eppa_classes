import AllThoseEPPA.Applications.KOrientations.EmbeddedSuccessorSourceRooted
import AllThoseEPPA.Applications.KOrientations.ClosedGraphDTraceIso

/-!
# Exact d-trace bridge from the original first-stage successor embedding

The first unrestricted EPPA witness B₀ is only an s-expansion.
Its embedded original source S is successor-closed, but need not be
closed under ambient higher-arity d-fibres. Therefore we must not
apply the full d-substructure inclusion theorem to S.

Any exact successor embedding A→B₀, however, is an induced graph
isomorphism from the whole original A to the successor-closed image S.
The general graph-determines-functions theorem upgrades this to a
full d-language embedding of d(A) into the *relative d-trace* on S.
There is no extra ambient d-closure assumption and all F_n are
transferred exactly in arbitrary arity.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The full graph d-structure and its d-trace on the whole vertex
set are exactly isomorphic. -/
noncomputable def dStructure_to_univ_dTrace
    {V : Type u} [Fintype V]
    (G : Digraph V) (k : ℕ) :
    Structure.Embedding dTrivialAction
      (dStructure G k) (dTraceStructure G k Set.univ) where
  lang := 1
  toFun := fun x => ⟨x, Set.mem_univ _⟩
  injective := by
    intro x y h
    exact congrArg Subtype.val h
  map_rel_iff := by
    intro n R xs
    cases R with
    | edge =>
        change G.edge (xs 0) (xs 1) ↔ G.edge (xs 0) (xs 1)
        exact Iff.rfl
  map_func := by
    intro n F xs
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      exact ⟨z.val, hz, Subtype.ext rfl⟩

/-- An exact embedding of successor expansions extends canonically
to all d-functions when the target is the relative d-trace on the
successor-closed image of the original vertices. -/
noncomputable def successorEmbedding_to_dTrace
    {U : Type u} {V : Type v} [Fintype U] [Fintype V]
    (A : Digraph U) (G : Digraph V) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    Structure.Embedding dTrivialAction
      (dStructure A k)
      (dTraceStructure G k (Set.range ι.toFun)) := by
  let t : (Set.univ : Set U) →
      {v : V // v ∈ Set.range ι.toFun} :=
    fun a => ⟨ι a.val, ⟨a.val, rfl⟩⟩
  have hInj : Function.Injective t := by
    intro a b h
    apply Subtype.ext
    apply ι.injective
    exact congrArg Subtype.val h
  have hSurj : Function.Surjective t := by
    intro z
    obtain ⟨a, ha⟩ := z.property
    refine ⟨⟨a, Set.mem_univ _⟩, ?_⟩
    apply Subtype.ext
    exact ha
  let e : (Set.univ : Set U) ≃
      {v : V // v ∈ Set.range ι.toFun} :=
    Equiv.ofBijective t ⟨hInj, hSurj⟩
  have hSourceSucc :
      ∀ x y : U, x ∈ (Set.univ : Set U) →
        A.edge x y → y ∈ (Set.univ : Set U) :=
    fun _ _ _ _ => Set.mem_univ _
  have hTargetSucc :
      ∀ x y : V, x ∈ Set.range ι.toFun →
        G.edge x y → y ∈ Set.range ι.toFun := by
    intro x y hx hxy
    exact successorEmbedding_image_successorClosed A G ι
      x y hx (G.reaches_of_edge hxy)
  have hEdge :
      ∀ x y : (Set.univ : Set U),
        A.edge x.val y.val ↔ G.edge (e x).val (e y).val := by
    intro x y
    exact (successorEmbedding_edge_iff A G ι x.val y.val).symm
  exact (closedGraph_dTraceEmbedding
      A G k Set.univ (Set.range ι.toFun)
      hSourceSucc hTargetSucc e hEdge).comp
      (dStructure_to_univ_dTrace A k)

end AllThoseEPPA.Applications.KOrientations
