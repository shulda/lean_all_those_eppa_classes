import AllThoseEPPA.TreeLikeHomEmbComposition

/-!
# Existential pushforward of Γ-structures along vertex maps

Given q:V→U and a structure A on V, interpret all relations
and set-valued function fibres on U by taking existential
direct images of original tuples and values.

Then q:A→q₊A is a genuine Γ-homomorphism with identity
language component. If f:A→B already is a Γ-homomorphism and
its vertex map factors as f=g∘q, the second map g:q₊A→B
is also a genuine Γ-homomorphism with language part f.lang.

This is a structural interface for the local closure collapse
in Proposition 11.3. It is essential NOT to conflate ordinary
homomorphisms with homomorphism-embeddings here: proving both
factors locally exact for the special closure collapse is
the remaining mathematical obligation.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x y
variable {L : Language.{u}} {V : Type v}
variable {U : Type w} {W : Type y}
variable {Γ : Type x} [Group Γ]

/-- Interpret tuples and set-valued functions by existential
pushforward along an arbitrary vertex map. -/
def pushforwardAlong
    (A : Structure L V) (q : V → U) :
    Structure L U where
  rel := by
    intro n R xs
    exact ∃ ys : Fin n → V, q ∘ ys = xs ∧ A.rel R ys
  func := by
    intro n F xs
    exact {z | ∃ ys : Fin n → V,
      q ∘ ys = xs ∧ z ∈ imageSet q (A.func F ys)}

namespace Homomorphism

/-- The source maps homomorphically into its existential
pushforward. No injectivity, surjectivity, or finite-carrier
assumption on q is required. -/
def toPushforward
    (act : L.Action Γ)
    (A : Structure L V) (q : V → U) :
    Homomorphism act A (A.pushforwardAlong q) where
  lang := 1
  toFun := q
  map_rel := by
    intro n R xs hx
    rw [act.onRel_one]
    change ∃ ys : Fin n → V, q ∘ ys = q ∘ xs ∧ A.rel R ys
    exact ⟨xs, rfl, hx⟩
  map_func := by
    intro n F xs z hz
    rw [act.onFunc_one]
    change ∃ ys : Fin n → V,
      q ∘ ys = q ∘ xs ∧ z ∈ imageSet q (A.func F ys)
    exact ⟨xs, rfl, hz⟩

/-- Universal descent of a Γ-homomorphism through its
vertex-level factorization. It preserves the complete
language component of f, even for nontrivial Γ actions. -/
def fromPushforward
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q) :
    Homomorphism act (A.pushforwardAlong q) B where
  lang := f.lang
  toFun := g
  map_rel := by
    intro n R xs hRel
    change (∃ ys : Fin n → V, q ∘ ys = xs ∧ A.rel R ys) at hRel
    obtain ⟨ys, hys, hR⟩ := hRel
    have hTuple : f.toFun ∘ ys = g ∘ xs := by
      calc
        f.toFun ∘ ys = (g ∘ q) ∘ ys := by rw [hFactor]
        _ = g ∘ (q ∘ ys) := by funext i; rfl
        _ = g ∘ xs := by rw [hys]
    simpa only [hTuple] using f.map_rel R ys hR
  map_func := by
    intro n F xs z hz
    obtain ⟨t, ht, rfl⟩ := hz
    change (∃ ys : Fin n → V,
      q ∘ ys = xs ∧ t ∈ imageSet q (A.func F ys)) at ht
    obtain ⟨ys, hys, ⟨a, ha, hqa⟩⟩ := ht
    have hTuple : f.toFun ∘ ys = g ∘ xs := by
      calc
        f.toFun ∘ ys = (g ∘ q) ∘ ys := by rw [hFactor]
        _ = g ∘ (q ∘ ys) := by funext i; rfl
        _ = g ∘ xs := by rw [hys]
    have hfMem :
        f a ∈ B.func (act.onFunc f.lang F) (f.toFun ∘ ys) :=
      f.map_func F ys ⟨a, ha, rfl⟩
    have hValue : g t = f a := by
      calc
        g t = g (q a) := by rw [hqa]
        _ = f a := (congrFun hFactor a).symm
    rw [hValue]
    simpa only [hTuple] using hfMem

/-- The descended map and the initial pushforward map
compose pointwise to the original homomorphism f. -/
theorem fromPushforward_comp_apply
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q) (a : V) :
    ((fromPushforward act f q g hFactor).comp
      (toPushforward act A q)) a = f a := by
  exact (congrFun hFactor a).symm

/-- Composition recovers f's Γ-language component as well. -/
theorem fromPushforward_comp_lang
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q) :
    ((fromPushforward act f q g hFactor).comp
      (toPushforward act A q)).lang = f.lang := by
  change f.lang * 1 = f.lang
  simp

end Homomorphism
end Structure
end AllThoseEPPA
