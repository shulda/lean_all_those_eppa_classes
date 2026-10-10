import AllThoseEPPA.TreeLikeTowerClosedProjections
import AllThoseEPPA.TreeLikeInducedIrreducibles

/-!
# Inducing a genuine homomorphism between closed projection images

The cycle-sparsening projection need not be injective on a whole
witness. Its restriction from a closed set of vertices to its
closed projected image is nevertheless a genuine structure
homomorphism, not merely a map between ambient vertex types.

We construct this restriction for an arbitrary homomorphism
whose source subset and target image are function-closed.
When the original homomorphism maps *complete* function fibres
onto the corresponding target fibres, the induced map does too.

The concrete one-step application uses the already proven exact
fibre law for the cycle-sparsening projection. This supplies
the typed maps needed for composing projections from a small
closed substructure down an actual finite sparsening tower.

No injectivity is asserted here: it holds only on irreducible
substructures, as will be handled separately.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- A homomorphism of ambient Γ-structures restricts to a
homomorphism from a closed induced substructure into the
structure induced on its closed direct image. -/
noncomputable def inducedClosedImage
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (S : Set V) (hS : A.IsClosed S)
    (hImage : B.IsClosed (imageSet f.toFun S)) :
    Homomorphism act (A.induce S hS)
      (B.induce (imageSet f.toFun S) hImage) where
  lang := f.lang
  toFun := fun x => ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩
  map_rel := by
    intro n R xs hRel
    have h := f.map_rel R (Subtype.val ∘ xs) hRel
    simpa only [Structure.induce, Function.comp_def] using h
  map_func := by
    intro n F xs
    rintro z ⟨y, hy, rfl⟩
    have hyA : y.1 ∈ A.func F (Subtype.val ∘ xs) := hy
    have hf : f y.1 ∈
        B.func (act.onFunc f.lang F) (f.toFun ∘ (Subtype.val ∘ xs)) :=
      f.map_func F (Subtype.val ∘ xs) ⟨y.1, hyA, rfl⟩
    change f y.1 ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ (Subtype.val ∘ xs))
    exact hf

/-- If a homomorphism maps every *whole* set-valued function
fibre exactly onto the target fibre, the induced map on any
closed source subset and its closed image also has this
**equality**, not merely the homomorphism inclusion. -/
theorem inducedClosedImage_exact_func
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hExact : ∀ {n : ℕ} (F : L.FuncSymbol n) (xs : Fin n → V),
      imageSet f.toFun (A.func F xs) =
        B.func (act.onFunc f.lang F) (f.toFun ∘ xs))
    (S : Set V) (hS : A.IsClosed S)
    (hImage : B.IsClosed (imageSet f.toFun S))
    {n : ℕ} (F : L.FuncSymbol n) (xs : Fin n → S) :
    imageSet (inducedClosedImage act f S hS hImage).toFun
        ((A.induce S hS).func F xs) =
      (B.induce (imageSet f.toFun S) hImage).func
        (act.onFunc (inducedClosedImage act f S hS hImage).lang F)
        ((inducedClosedImage act f S hS hImage).toFun ∘ xs) := by
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzA : z.1 ∈ A.func F (Subtype.val ∘ xs) := hz
    have hzB : f z.1 ∈ B.func (act.onFunc f.lang F)
        (f.toFun ∘ (Subtype.val ∘ xs)) := by
      rw [← hExact F (Subtype.val ∘ xs)]
      exact ⟨z.1, hzA, rfl⟩
    have hyB : y.1 ∈ B.func (act.onFunc f.lang F)
        (f.toFun ∘ (Subtype.val ∘ xs)) := by
      have hv : f z.1 = y.1 := congrArg Subtype.val hzy
      rwa [← hv]
    change y.1 ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ (Subtype.val ∘ xs))
    exact hyB
  · intro hy
    have hyB : y.1 ∈
        B.func (act.onFunc f.lang F)
          (f.toFun ∘ (Subtype.val ∘ xs)) := by
      change y.1 ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ (Subtype.val ∘ xs)) at hy
      exact hy
    rw [← hExact F (Subtype.val ∘ xs)] at hyB
    obtain ⟨z, hzA, hzB⟩ := hyB
    have hzS : z ∈ S := hS F (Subtype.val ∘ xs)
      (fun i => (xs i).2) hzA
    refine ⟨⟨z, hzS⟩, ?_, ?_⟩
    · exact hzA
    · apply Subtype.ext
      exact hzB

end Homomorphism
end Structure

namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

/-- A concrete *typed* homomorphism from a closed subset
at a new sparsening stage to its actual closed image in the
preceding stage. It is the restricted canonical projection,
not an independently chosen map. -/
noncomputable def ClosedStageSubset.projectHom
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.next act A E hfix hcomplete s)) :
    Structure.Homomorphism act
      ((FaithfulSparseningStage.next act A E hfix hcomplete s).model.induce
        T.support T.closed)
      (s.model.induce
        (ClosedStageSubset.project act A E hfix hcomplete s T).support
        (ClosedStageSubset.project act A E hfix hcomplete s T).closed) := by
  letI : Finite s.Carrier := s.finiteCarrier
  exact Structure.Homomorphism.inducedClosedImage act
    (FaithfulSparseningStage.nextProjection act A E hfix hcomplete s)
    T.support T.closed
    (ClosedStageSubset.project act A E hfix hcomplete s T).closed

/-- The concrete closed-stage projection exactly maps the
whole fibre of every unary function onto the corresponding
fibre of its projected induced substructure. -/
theorem ClosedStageSubset.projectHom_exact_func
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (T : ClosedStageSubset act A
      (FaithfulSparseningStage.next act A E hfix hcomplete s))
    {n : ℕ} (F : L.FuncSymbol n)
    (xs : Fin n → T.support) :
    Structure.imageSet
      (ClosedStageSubset.projectHom act A E hfix hcomplete s T).toFun
      (((FaithfulSparseningStage.next act A E hfix hcomplete s).model.induce
        T.support T.closed).func F xs) =
    (s.model.induce
      (ClosedStageSubset.project act A E hfix hcomplete s T).support
      (ClosedStageSubset.project act A E hfix hcomplete s T).closed).func
      (act.onFunc (ClosedStageSubset.projectHom
        act A E hfix hcomplete s T).lang F)
      ((ClosedStageSubset.projectHom
        act A E hfix hcomplete s T).toFun ∘ xs) := by
  letI : Finite s.Carrier := s.finiteCarrier
  exact Structure.Homomorphism.inducedClosedImage_exact_func act
    (FaithfulSparseningStage.nextProjection act A E hfix hcomplete s)
    (FaithfulSparseningStage.nextProjection_exact_functions
      act A E hfix hcomplete s)
    T.support T.closed
    (ClosedStageSubset.project act A E hfix hcomplete s T).closed
    F xs

end TreeLike
end AllThoseEPPA
