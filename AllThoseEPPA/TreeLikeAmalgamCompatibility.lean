import AllThoseEPPA.TreeLikeAmalgamRelabel

/-!
# Structural compatibility on the glued interface

A free amalgam cannot be built merely by identifying vertices.
The two Γ-structure embeddings of the common substructure must
give *identical interpretations* on that overlap, including
all set-valued function fibres.

Assume f and g are embeddings whose language components agree
(after the relabelling from `TreeLikeAmalgamRelabel`). This file
proves:

* a tuple represented on both sides comes from a tuple in the
  common carrier;
* the two structures agree on relations over that tuple;
* the exact images of their function-value sets agree in the
  concrete amalgam carrier.

This is the coherence condition for the pending direct
construction of a genuine free-amalgamation structure, not an
additional hypothesis about relations or functions.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- If all coordinates of two tuples have the same image in the
amalgam carrier, then both tuples come from one common-interface
tuple. This also covers arity zero without a special case. -/
theorem amalgam_tuple_overlap
    (f : I → X) (g : I → Y)
    (hg : Function.Injective g)
    {n : ℕ} (xs : Fin n → X) (ys : Fin n → Y)
    (hTuple :
      amalgamLeft f g ∘ xs = amalgamRight f g ∘ ys) :
    ∃ cs : Fin n → I, xs = f ∘ cs ∧ ys = g ∘ cs := by
  classical
  have hPoint (i : Fin n) :
      ∃ c : I, xs i = f c ∧ ys i = g c :=
    (amalgamLeft_eq_amalgamRight_iff f g hg (xs i) (ys i)).mp
      (congrFun hTuple i)
  choose cs hcs using hPoint
  refine ⟨cs, ?_, ?_⟩
  · funext i
    exact (hcs i).1
  · funext i
    exact (hcs i).2

/-- Γ-embeddings with equal language components induce the same
relation interpretation on every tuple of the shared substructure. -/
theorem amalgam_overlap_relation
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang)
    {n : ℕ} (R : L.RelSymbol n) (cs : Fin n → I) :
    B₁.rel R (f.toFun ∘ cs) ↔
      B₂.rel R (g.toFun ∘ cs) := by
  let R₀ : L.RelSymbol n := act.onRel f.lang⁻¹ R
  have hF : act.onRel f.lang R₀ = R := by
    change act.onRel f.lang (act.onRel f.lang⁻¹ R) = R
    rw [← act.onRel_mul]
    simp
  have hG : act.onRel g.lang R₀ = R := by
    rw [← hLang]
    exact hF
  have hf := f.map_rel_iff R₀ cs
  have hg := g.map_rel_iff R₀ cs
  rw [hF] at hf
  rw [hG] at hg
  exact hf.trans hg.symm

/-- Exact agreement of the *images in the amalgam carrier*
of function fibres on the common interface.

Unlike a mere homomorphism argument, this equality ensures that
adjoining the two interpretations by union will still give
structure **embeddings** on both sides. -/
theorem amalgam_overlap_function
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang)
    {n : ℕ} (F : L.FuncSymbol n) (cs : Fin n → I) :
    Structure.imageSet (amalgamLeft f.toFun g.toFun)
      (B₁.func F (f.toFun ∘ cs)) =
    Structure.imageSet (amalgamRight f.toFun g.toFun)
      (B₂.func F (g.toFun ∘ cs)) := by
  let F₀ : L.FuncSymbol n := act.onFunc f.lang⁻¹ F
  have hF : act.onFunc f.lang F₀ = F := by
    change act.onFunc f.lang (act.onFunc f.lang⁻¹ F) = F
    rw [← act.onFunc_mul]
    simp
  have hG : act.onFunc g.lang F₀ = F := by
    rw [← hLang]
    exact hF
  have hf : Structure.imageSet f.toFun (C.func F₀ cs) =
      B₁.func F (f.toFun ∘ cs) := by
    simpa only [hF] using f.map_func F₀ cs
  have hg : Structure.imageSet g.toFun (C.func F₀ cs) =
      B₂.func F (g.toFun ∘ cs) := by
    simpa only [hG] using g.map_func F₀ cs
  have hComm :
      amalgamLeft f.toFun g.toFun ∘ f.toFun =
      amalgamRight f.toFun g.toFun ∘ g.toFun := by
    funext i
    exact (amalgamRight_glued f.toFun g.toFun g.injective i).symm
  calc
    Structure.imageSet (amalgamLeft f.toFun g.toFun)
        (B₁.func F (f.toFun ∘ cs)) =
      Structure.imageSet (amalgamLeft f.toFun g.toFun)
        (Structure.imageSet f.toFun (C.func F₀ cs)) := by
        rw [hf]
    _ = Structure.imageSet
          (amalgamLeft f.toFun g.toFun ∘ f.toFun)
          (C.func F₀ cs) :=
        (Structure.imageSet_comp
          (amalgamLeft f.toFun g.toFun) f.toFun (C.func F₀ cs)).symm
    _ = Structure.imageSet
          (amalgamRight f.toFun g.toFun ∘ g.toFun)
          (C.func F₀ cs) := by rw [hComm]
    _ = Structure.imageSet (amalgamRight f.toFun g.toFun)
          (Structure.imageSet g.toFun (C.func F₀ cs)) :=
        Structure.imageSet_comp
          (amalgamRight f.toFun g.toFun) g.toFun (C.func F₀ cs)
    _ = Structure.imageSet (amalgamRight f.toFun g.toFun)
          (B₂.func F (g.toFun ∘ cs)) := by
        rw [hg]

end TreeLike
end AllThoseEPPA
