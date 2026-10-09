import AllThoseEPPA.FaithfulExtension

/-!
# Partial isomorphisms from embedded induced substructures

This packages an embedding of an induced closed substructure back into the
ambient structure as a partial automorphism of the ambient structure.
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w

variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {V : Type w}
variable (act : L.Action Γ)
variable (B : Structure L V)

/-- The range of an embedding of an induced substructure, as a subset of the
ambient carrier. -/
def inducedEmbeddingRange
    (S : Set V) (hS : B.IsClosed S)
    (f : Structure.Embedding act (B.induce S hS) B) :
    Set V :=
  Set.range f

/-- An embedding of an induced substructure is an equivalence from its
carrier onto its range. -/
noncomputable def inducedEmbeddingRangeEquiv
    (S : Set V) (hS : B.IsClosed S)
    (f : Structure.Embedding act (B.induce S hS) B) :
    S ≃ inducedEmbeddingRange act B S hS f :=
  Equiv.ofBijective
    (fun x =>
      ⟨f x, ⟨x, rfl⟩⟩)
    ⟨by
      intro x y hxy
      apply Subtype.ext
      exact congrArg Subtype.val
        (f.injective (congrArg Subtype.val hxy)),
     by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩⟩

/-- Package an embedding of a closed induced substructure into the ambient
structure as a partial automorphism. -/
noncomputable def partialAutomorphismOfInducedEmbedding
    (S : Set V) (hS : B.IsClosed S)
    (f : Structure.Embedding act (B.induce S hS) B) :
    Structure.PartialAutomorphism act B := by
  classical
  let T : Set V :=
    inducedEmbeddingRange act B S hS f
  let e : S ≃ T :=
    inducedEmbeddingRangeEquiv act B S hS f
  let pe : PartialEquiv V V :=
    partialEquivOfSubtypeEquiv
      S T e (Equiv.refl V)
  refine
    { lang := f.lang
      toPartialEquiv := pe
      source_closed := ?_
      target_closed := ?_
      map_rel_iff := ?_
      map_func := ?_ }
  · change B.IsClosed S
    exact hS
  · change B.IsClosed T
    exact
      (embedding_range_isClosed
        act (B.induce S hS) B f)
  · intro n R xs hxs
    let xsS : Fin n → S :=
      fun i => ⟨xs i, by
        simpa [pe] using hxs i⟩
    have hpe :
        pe ∘ xs = f ∘ xsS := by
      funext i
      exact
        partialEquivOfSubtypeEquiv_apply_of_mem
          S T e (Equiv.refl V) (xsS i).2
    have hf := f.map_rel_iff R xsS
    change
      B.rel (act.onRel f.lang R) (pe ∘ xs) ↔
        B.rel R xs
    rw [hpe]
    simpa [Structure.induce, xsS, Function.comp_def] using hf
  · intro n F xs hxs
    let xsS : Fin n → S :=
      fun i => ⟨xs i, by
        simpa [pe] using hxs i⟩
    have hpe :
        pe ∘ xs = f ∘ xsS := by
      funext i
      exact
        partialEquivOfSubtypeEquiv_apply_of_mem
          S T e (Equiv.refl V) (xsS i).2
    have hf := f.map_func F xsS
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzS : z ∈ S := by
        apply hS F xs
        · intro i
          exact (xsS i).2
        · exact hz
      have hpez :
          pe z = f (⟨z, hzS⟩ : S) :=
        partialEquivOfSubtypeEquiv_apply_of_mem
          S T e (Equiv.refl V) hzS
      rw [hpez]
      have himg :
          f (⟨z, hzS⟩ : S) ∈
            Structure.imageSet f
              ((B.induce S hS).func F xsS) := by
        refine ⟨⟨z, hzS⟩, ?_, rfl⟩
        simpa [Structure.induce, xsS, Function.comp_def] using hz
      rw [hf] at himg
      simpa [hpe] using himg
    · intro hy
      have hy' :
          y ∈
            B.func (act.onFunc f.lang F)
              (f ∘ xsS) := by
        simpa [hpe] using hy
      rw [← hf] at hy'
      rcases hy' with ⟨z, hz, hzy⟩
      have hzB :
          z.1 ∈ B.func F xs := by
        simpa [Structure.induce, xsS, Function.comp_def] using hz
      refine ⟨z.1, hzB, ?_⟩
      have hpez :
          pe z.1 = f z :=
        partialEquivOfSubtypeEquiv_apply_of_mem
          S T e (Equiv.refl V) z.2
      exact hpez.trans hzy

@[simp] theorem partialAutomorphismOfInducedEmbedding_source
    (S : Set V) (hS : B.IsClosed S)
    (f : Structure.Embedding act (B.induce S hS) B) :
    (partialAutomorphismOfInducedEmbedding
      act B S hS f).source = S :=
  rfl

@[simp] theorem partialAutomorphismOfInducedEmbedding_target
    (S : Set V) (hS : B.IsClosed S)
    (f : Structure.Embedding act (B.induce S hS) B) :
    (partialAutomorphismOfInducedEmbedding
      act B S hS f).target =
      inducedEmbeddingRange act B S hS f :=
  rfl

theorem partialAutomorphismOfInducedEmbedding_apply
    (S : Set V) (hS : B.IsClosed S)
    (f : Structure.Embedding act (B.induce S hS) B)
    {x : V} (hx : x ∈ S) :
    partialAutomorphismOfInducedEmbedding
        act B S hS f x =
      f (⟨x, hx⟩ : S) := by
  exact
    partialEquivOfSubtypeEquiv_apply_of_mem
      S (inducedEmbeddingRange act B S hS f)
      (inducedEmbeddingRangeEquiv act B S hS f)
      (Equiv.refl V) hx

end Faithful
end AllThoseEPPA
