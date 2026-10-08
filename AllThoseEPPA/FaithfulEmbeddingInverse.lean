import AllThoseEPPA.FaithfulInducedPartialIso

/-!
# Inverting an embedding on a closed subset of its range
-/

namespace AllThoseEPPA
namespace Faithful

universe u v w z

variable {L : Language.{u}}
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type z}
variable (act : L.Action Γ)
variable {A : Structure L V} {B : Structure L W}

/-- If a closed subset of the target of an embedding lies in its range, the
induced structure on that subset embeds back into the source. -/
noncomputable def embeddingInverseOnClosedSubset
    (f : Structure.Embedding act A B)
    (T : Set W) (hT : B.IsClosed T)
    (hsub : T ⊆ Set.range f) :
    Structure.Embedding act (B.induce T hT) A := by
  classical
  let preimage : T → V :=
    fun x => Classical.choose (hsub x.2)
  have hpreimage (x : T) :
      f (preimage x) = x.1 :=
    Classical.choose_spec (hsub x.2)
  refine
    { lang := f.lang⁻¹
      toFun := preimage
      injective := ?_
      map_rel_iff := ?_
      map_func := ?_ }
  · intro x y hxy
    apply Subtype.ext
    rw [← hpreimage x, ← hpreimage y]
    exact congrArg f.toFun hxy
  · intro n R xs
    let as : Fin n → V := fun i => preimage (xs i)
    have htuple :
        f.toFun ∘ as = Subtype.val ∘ xs := by
      funext i
      exact hpreimage (xs i)
    have hf :=
      f.map_rel_iff (act.onRel f.lang⁻¹ R) as
    have hsym :
        act.onRel f.lang (act.onRel f.lang⁻¹ R) = R := by
      simp [← Language.Action.onRel_mul]
    rw [hsym, htuple] at hf
    change
      A.rel (act.onRel f.lang⁻¹ R) as ↔
        B.rel R (Subtype.val ∘ xs)
    exact hf.symm
  · intro n F xs
    let as : Fin n → V := fun i => preimage (xs i)
    let F₀ : L.FuncSymbol n := act.onFunc f.lang⁻¹ F
    have htuple :
        f.toFun ∘ as = Subtype.val ∘ xs := by
      funext i
      exact hpreimage (xs i)
    have hf := f.map_func F₀ as
    have hsym :
        act.onFunc f.lang F₀ = F := by
      simp [F₀, ← Language.Action.onFunc_mul]
    rw [hsym, htuple] at hf
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxB :
          x.1 ∈ B.func F (Subtype.val ∘ xs) := by
        exact hx
      have hpxB :
          f (preimage x) ∈
            B.func F (Subtype.val ∘ xs) := by
        rw [hpreimage x]
        exact hxB
      rw [← hf] at hpxB
      rcases hpxB with ⟨b, hb, hfb⟩
      have hbpre : b = preimage x :=
        f.injective hfb
      simpa [F₀, as, hbpre] using hb
    · intro ha
      have himg :
          f a ∈
            Structure.imageSet f.toFun (A.func F₀ as) :=
        ⟨a, by simpa [F₀, as] using ha, rfl⟩
      rw [hf] at himg
      have hfaT : f a ∈ T :=
        hT F (Subtype.val ∘ xs)
          (fun i => (xs i).2) himg
      let x : T := ⟨f a, hfaT⟩
      refine ⟨x, ?_, ?_⟩
      · exact himg
      · exact f.injective (hpreimage x)

end Faithful
end AllThoseEPPA
