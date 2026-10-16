import AllThoseEPPA.Applications.KOrientations.FirstStageSourceDTraceEquiv

/-!
# Full original d(A) as the intrinsic d-trace inside the first witness B₀

The actual source of Theorem thm:DF is dStructure A k, whose
carrier is the ORIGINAL finite graph A, not the subtype
Set.univ, nor an artificial unary-function encoding.

A genuine first-stage successor embedding ι:A₀↪B₀ identifies
all original vertices with their exact embedded image S⊆B₀.
The latter is successor-closed, but not necessarily closed under
the ambient all-arity F_n of B₀. The CORRECT induced d-structure
on S is the intrinsic dTraceStructure.

This file first exhibits the actual entire d(A) as a bijective
full d-language embedding into its d-trace on Set.univ. Then
it composes with the independently constructed exact graph-
induced FULL d-trace embedding of old A into S⊆B₀, yielding
a bijective full d-language embedding of the ORIGINAL input
d(A) into the correct first-stage intrinsic d-trace.

These are not merely graph or unary successor maps: exact
set-valued outputs of every arbitrarily high-arity F_n are
preserved AND reflected. Crucially no ambient d-closedness of
the embedded old source S is asserted.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u v

/-- The genuine full d-language original structure is exactly
the intrinsic d-trace on the entire original carrier, with
only the obvious harmless subtype Set.univ inserted. -/
noncomputable def dStructure_univTraceEmbedding
    {V : Type u} [Fintype V]
    (A : Digraph V) (k : ℕ) :
    Structure.Embedding dTrivialAction
      (dStructure A k)
      (dTraceStructure A k (Set.univ : Set V)) where
  lang := 1
  toFun := fun x => ⟨x, Set.mem_univ x⟩
  injective := by
    intro x y h
    exact congrArg Subtype.val h
  map_rel_iff := by
    intro n R xs
    cases R with
    | edge => rfl
  map_func := by
    intro n F xs
    ext z
    constructor
    · rintro ⟨x, hx, hEq⟩
      change z.val ∈ (dStructure A k).func F xs
      have hz : x = z.val := congrArg Subtype.val hEq
      rw [← hz]
      exact hx
    · intro hz
      change z.val ∈ (dStructure A k).func F xs at hz
      refine ⟨z.val, hz, ?_⟩
      apply Subtype.ext
      rfl

/-- The all-vertex d-trace model covers exactly the original
finite vertex set, with no lost or invented vertices. -/
theorem dStructure_univTraceEmbedding_bijective
    {V : Type u} [Fintype V]
    (A : Digraph V) (k : ℕ) :
    Function.Bijective (dStructure_univTraceEmbedding A k).toFun := by
  constructor
  · exact (dStructure_univTraceEmbedding A k).injective
  · intro z
    exact ⟨z.val, Subtype.ext rfl⟩

/-- A genuine successor-language embedding of the original
finite graph into its first EPPA witness automatically induces
an ACTUAL full d-language bijective embedding from d(A) into
the intrinsic d-trace on the embedded old source in B₀. -/
noncomputable def firstStageFullDSourceEmbedding
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    Structure.Embedding dTrivialAction
      (dStructure A k)
      (dTraceStructure G k (Set.range ι.toFun)) :=
  (firstStageSourceDTraceEmbedding A G k ι).comp
    (dStructure_univTraceEmbedding A k)

/-- The full d-language embedding above is an isomorphism on
its honest intrinsic SOURCE d-trace carrier; surjectivity
is never asserted onto ambient B₀, which may have new points. -/
theorem firstStageFullDSourceEmbedding_bijective
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (A : Digraph V) (G : Digraph W) (k : ℕ)
    (ι : Structure.Embedding successorAction
      (successorStructure A) (successorStructure G)) :
    Function.Bijective
      (firstStageFullDSourceEmbedding A G k ι).toFun := by
  constructor
  · exact (firstStageFullDSourceEmbedding A G k ι).injective
  · intro z
    obtain ⟨x, hx⟩ :=
      (firstStageSourceDTraceEmbedding_bijective A G k ι).2 z
    refine ⟨x.val, ?_⟩
    change (firstStageSourceDTraceEmbedding A G k ι).toFun
      ((dStructure_univTraceEmbedding A k).toFun x.val) = z
    have h : (dStructure_univTraceEmbedding A k).toFun x.val = x :=
      Subtype.ext rfl
    rw [h]
    exact hx

end AllThoseEPPA.Applications.KOrientations
