import AllThoseEPPA.FaithfulFaithfulness

/-!
# Embedding represented by a partial automorphism on its source
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w

variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {V : Type w}
variable (act : L.Action Γ)
variable {A : Structure L V}

/-- Restrict a partial automorphism to its source and regard it as an
embedding of the induced source substructure into the ambient structure. -/
noncomputable def partialAutomorphismSourceEmbedding
    (p : Structure.PartialAutomorphism act A) :
    Structure.Embedding act
      (A.induce p.source p.source_closed) A where
  lang := p.lang
  toFun := fun x => p x.1
  injective := by
    intro x y hxy
    apply Subtype.ext
    have h :=
      congrArg p.toPartialEquiv.symm hxy
    simpa [p.toPartialEquiv.left_inv x.2,
      p.toPartialEquiv.left_inv y.2] using h
  map_rel_iff := by
    intro n R xs
    have hp :=
      p.map_rel_iff R
        (fun i => (xs i).1)
        (fun i => (xs i).2)
    simpa [Structure.induce, Function.comp_def] using hp
  map_func := by
    intro n F xs
    let ys : Fin n → V := fun i => (xs i).1
    have hys : ∀ i, ys i ∈ p.source :=
      fun i => (xs i).2
    have hp := p.map_func F ys hys
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxA : x.1 ∈ A.func F ys := by
        simpa [Structure.induce, ys, Function.comp_def] using hx
      have himg :
          p x.1 ∈
            Structure.imageSet p.toPartialEquiv
              (A.func F ys) :=
        ⟨x.1, hxA, rfl⟩
      rw [hp] at himg
      simpa [ys, Function.comp_def] using himg
    · intro hz
      have hz' :
          z ∈
            A.func (act.onFunc p.lang F)
              (p.toPartialEquiv ∘ ys) := by
        simpa [ys, Function.comp_def] using hz
      rw [← hp] at hz'
      rcases hz' with ⟨x, hx, hpx⟩
      have hxSource : x ∈ p.source :=
        p.source_closed F ys hys hx
      refine ⟨⟨x, hxSource⟩, ?_, ?_⟩
      · simpa [Structure.induce, ys, Function.comp_def] using hx
      · exact hpx

end Faithful
end AllThoseEPPA
