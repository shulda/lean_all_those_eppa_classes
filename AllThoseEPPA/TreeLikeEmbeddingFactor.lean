import AllThoseEPPA.Map
import AllThoseEPPA.Automorphism

/-!
# Factoring an embedding through another embedding

This generic lemma isolates the algebra behind extracting an
embedding of an irreducible substructure of a faithful EPPA witness
into the distinguished A.

Suppose j : A ↪ B and g : C ↪ B are embeddings, and the image
of g lies in the image of j. Then g factors through j by an
embedding f : C ↪ A. The language component is exactly
j.lang⁻¹ * g.lang. The proof works with arbitrary arity,
genuine set-valued functions, and nontrivial language actions.

This factorization is a prerequisite for deriving the full local
hypothesis of the paper's Lemma `lem:cuts` from irreducible-
structure faithfulness.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x} {X : Type y}

/-- Direct image of subsets under an injective map is injective,
even when the domain and codomain have different carrier types. -/
theorem imageSet_injective_of_injective
    (f : V → W) (hf : Function.Injective f) :
    Function.Injective (imageSet f) := by
  intro S T hST
  ext x
  constructor
  · intro hx
    have hfx : f x ∈ imageSet f T := by
      rw [← hST]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfy⟩ := hfx
    have hEq : y = x := hf hfy
    simpa only [hEq] using hy
  · intro hx
    have hfx : f x ∈ imageSet f S := by
      rw [hST]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfy⟩ := hfx
    have hEq : y = x := hf hfy
    simpa only [hEq] using hy

/-- Factor g : C ↪ B through j : A ↪ B, provided every point in
g(C) is already in j(A). The resulting map is an embedding, not
merely an injective homomorphism; its function-value preservation
uses equality of images under j and injectivity of j. -/
noncomputable def Embedding.factorThrough
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W} {C : Structure L X}
    (j : Embedding act A B)
    (g : Embedding act C B)
    (hRange : ∀ c : X, ∃ a : V, j a = g c) :
    Embedding act C A := by
  classical
  let f : X → V := fun c => Classical.choose (hRange c)
  have hf (c : X) : j (f c) = g c :=
    Classical.choose_spec (hRange c)
  have hfComp : j.toFun ∘ f = g.toFun := by
    funext c
    exact hf c
  let h : Γ := j.lang⁻¹ * g.lang
  have hh : j.lang * h = g.lang := by
    simp only [h, mul_inv_cancel_left]
  refine
    { lang := h
      toFun := f
      injective := ?_
      map_rel_iff := ?_
      map_func := ?_ }
  · intro a b heq
    apply g.injective
    calc
      g a = j (f a) := (hf a).symm
      _ = j (f b) := by rw [heq]
      _ = g b := hf b
  · intro n R xs
    have hs : act.onRel j.lang (act.onRel h R) =
        act.onRel g.lang R := by
      rw [← act.onRel_mul, hh]
    have ht : j.toFun ∘ (f ∘ xs) = g.toFun ∘ xs := by
      funext i
      exact hf (xs i)
    have hj := j.map_rel_iff (act.onRel h R) (f ∘ xs)
    have hj' :
        B.rel (act.onRel g.lang R) (g.toFun ∘ xs) ↔
          A.rel (act.onRel h R) (f ∘ xs) := by
      simpa only [hs, ht] using hj
    exact hj'.symm.trans (g.map_rel_iff R xs)
  · intro n F xs
    have hs : act.onFunc j.lang (act.onFunc h F) =
        act.onFunc g.lang F := by
      rw [← act.onFunc_mul, hh]
    have ht : j.toFun ∘ (f ∘ xs) = g.toFun ∘ xs := by
      funext i
      exact hf (xs i)
    have hEq :
        imageSet j.toFun (imageSet f (C.func F xs)) =
          imageSet j.toFun (A.func (act.onFunc h F) (f ∘ xs)) := by
      calc
        imageSet j.toFun (imageSet f (C.func F xs)) =
            imageSet (j.toFun ∘ f) (C.func F xs) :=
          (imageSet_comp j.toFun f (C.func F xs)).symm
        _ = imageSet g.toFun (C.func F xs) := by rw [hfComp]
        _ = B.func (act.onFunc g.lang F) (g.toFun ∘ xs) :=
          g.map_func F xs
        _ = B.func (act.onFunc j.lang (act.onFunc h F))
              (j.toFun ∘ (f ∘ xs)) := by rw [hs, ht]
        _ = imageSet j.toFun (A.func (act.onFunc h F) (f ∘ xs)) :=
          (j.map_func (act.onFunc h F) (f ∘ xs)).symm
    exact imageSet_injective_of_injective j.toFun j.injective hEq

end Structure
end AllThoseEPPA
