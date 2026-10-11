import AllThoseEPPA.StrongCompletionPushforwardFunctionFibres

/-!
# Unary weak fibre compatibility implies exact fibre congruence

The local closure-collapse construction (PR #166) proves a
pointwise compatibility law for *pairs* of unary function
outputs: if the inputs have equal quotient image and two
outputs have equal f-image, the outputs also have equal
quotient image.

At first this seems weaker than the full function-fibre
congruence required to make the canonical quotient preserve
whole set-valued fibres by equality.

In a language with unary functions, the gap closes:
because f is a Γ-homomorphism-embedding, its restrictions to
the irreducible closures of the respective single inputs
preserve the entire function fibre exactly. Equal quotient
input tuples thus have *identical f-images of output fibres*.
The pointwise compatibility then makes their q-images equal.

This is the missing bridge between the explicit closure
collapse and the general quotient closure-preservation
machinery. There is no finiteness, global injectivity, or
trivial-language-action assumption.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {U : Type x} {W : Type y}

/-- Weak fibre compatibility upgrades to exact equality of
whole quotient function fibres whenever f is a
Γ-homomorphism-embedding with unary set-valued functions.

The premise is the quantified pointwise condition later
established for the specific one-point-closure collapse. -/
theorem functionFibresCompatible_of_unary_weak
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (hWeak :
      ∀ {n : ℕ} (F : L.FuncSymbol n)
        (xs ys : Fin n → V),
        q ∘ xs = q ∘ ys →
        ∀ (a : V), a ∈ A.func F xs →
        ∀ (b : V), b ∈ A.func F ys →
          f a = f b → q a = q b) :
    A.FunctionFibresCompatible q := by
  intro n F xs ys hQ
  have hn : n = 1 := Language.HasUnaryFunctions.arity_eq_one F
  subst n
  have hFTuple : f.toFun ∘ xs = f.toFun ∘ ys := by
    calc
      f.toFun ∘ xs = (g ∘ q) ∘ xs := by rw [hFactor]
      _ = g ∘ (q ∘ xs) := by funext i; rfl
      _ = g ∘ (q ∘ ys) := by rw [hQ]
      _ = (g ∘ q) ∘ ys := by funext i; rfl
      _ = f.toFun ∘ ys := by rw [hFactor]
  have hFx : imageSet f.toFun (A.func F xs) =
      B.func (act.onFunc f.lang F) (f.toFun ∘ xs) := by
    let S : Set V := A.closureAtSet (xs 0)
    have hClosed : A.IsClosed S := A.isClosed_closureSet {xs 0}
    have hIrr : (A.induce S hClosed).IsIrreducible :=
      A.closureAt_isIrreducible (xs 0)
    exact (hf S hClosed hIrr).2.2 F xs (by
      intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact A.mem_closureAtSet (xs 0))
  have hFy : imageSet f.toFun (A.func F ys) =
      B.func (act.onFunc f.lang F) (f.toFun ∘ ys) := by
    let S : Set V := A.closureAtSet (ys 0)
    have hClosed : A.IsClosed S := A.isClosed_closureSet {ys 0}
    have hIrr : (A.induce S hClosed).IsIrreducible :=
      A.closureAt_isIrreducible (ys 0)
    exact (hf S hClosed hIrr).2.2 F ys (by
      intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact A.mem_closureAtSet (ys 0))
  have hFImages :
      imageSet f.toFun (A.func F xs) =
      imageSet f.toFun (A.func F ys) := by
    calc
      imageSet f.toFun (A.func F xs) =
          B.func (act.onFunc f.lang F) (f.toFun ∘ xs) := hFx
      _ = B.func (act.onFunc f.lang F) (f.toFun ∘ ys) := by rw [hFTuple]
      _ = imageSet f.toFun (A.func F ys) := hFy.symm
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hfMem : f a ∈ imageSet f.toFun (A.func F ys) := by
      rw [← hFImages]
      exact ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hfb⟩ := hfMem
    exact ⟨b, hb, (hWeak F xs ys hQ a ha b hb hfb.symm).symm⟩
  · rintro ⟨b, hb, rfl⟩
    have hfMem : f b ∈ imageSet f.toFun (A.func F xs) := by
      rw [hFImages]
      exact ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hfa⟩ := hfMem
    exact ⟨a, ha, (hWeak F ys xs hQ.symm b hb a ha hfa.symm).symm⟩

end Homomorphism
end Structure
end AllThoseEPPA
