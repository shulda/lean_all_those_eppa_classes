import AllThoseEPPA.StrongCompletionSafeDescent
import AllThoseEPPA.StrongCompletionPushforwardLocalExact

/-!
# The quotient map into the controlled saturation is a homomorphism-embedding

Let f:A→B be a Γ-homomorphism-embedding with underlying
factorization f = g∘q. Endow the intermediate carrier U
with the *controlled* relation saturation: R(xs) holds in U
iff R holds on its g-image AND g is injective on the
functionally generated closure of xs.

If the function fibres of A are congruent under q, the
quotient homomorphism q:A→U is itself a homomorphism-embedding:

* q is locally injective because its composite f is;
* it reflects relations because f reflects them;
* it preserves positive relations because the generated
  closure of a realized relation tuple is irreducible in A,
  and its q-image is the generated closure in U;
* its function fibres agree by quotient congruence.

This is the previously missing *first-factor* half of the
saturated factorization. The companion theorem proves the
second factor is a homomorphism-embedding for unary
functions. Both directions remain fully compatible with
arbitrary Γ-language permutations.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} {U : Type x} {W : Type y}

/-- Controlled saturation and arbitrary generated closures
commute with a quotient satisfying the exact congruence
condition, on the range of any source tuple. -/
theorem safeSaturation_tupleClosure_eq_image
    (act : L.Action Γ)
    (A : Structure L V) (q : V → U)
    (hCompat : A.FunctionFibresCompatible q)
    (B : Structure L W) (g : U → W) (lang : Γ)
    {n : ℕ} (xs : Fin n → V) :
    (safeRelationSaturation act A q B g lang).closureSet
        (Set.range (q ∘ xs)) =
      imageSet q (A.closureSet (Set.range xs)) := by
  have h := A.pushforward_image_closureSet_eq_of_compatible
    act q hCompat (Set.range xs)
  have hRange : imageSet q (Set.range xs) =
      Set.range (q ∘ xs) := by
    ext z
    constructor
    · rintro ⟨a, ⟨i, ha⟩, hqa⟩
      refine ⟨i, ?_⟩
      change q (xs i) = z
      rw [ha]
      exact hqa
    · rintro ⟨i, hi⟩
      exact ⟨xs i, ⟨i, rfl⟩, hi⟩
  rw [hRange] at h
  change (A.pushforwardAlong q).closureSet
    (Set.range (q ∘ xs)) =
    imageSet q (A.closureSet (Set.range xs))
  exact h.symm

/-- The original A is a Γ-homomorphic image inside the
controlled saturation. Its relation preservation is
nontrivial, and uses injectivity on primitive relation
closures transported through the exact congruence. -/
def toSafeRelationSaturation
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (hCompat : A.FunctionFibresCompatible q) :
    Homomorphism act A (safeRelationSaturation act A q B g f.lang) where
  lang := 1
  toFun := q
  map_rel := by
    intro n R xs hRel
    rw [act.onRel_one]
    have hB : B.rel (act.onRel f.lang R) (g ∘ (q ∘ xs)) := by
      have h := f.map_rel R xs hRel
      simpa only [hFactor, Function.comp_assoc] using h
    have hInj : Set.InjOn g
        ((safeRelationSaturation act A q B g f.lang).closureSet
          (Set.range (q ∘ xs))) := by
      rw [safeSaturation_tupleClosure_eq_image act A q hCompat
        B g f.lang xs]
      exact f.descended_injOn_image_relationClosure
        act hf q g hFactor R xs hRel
    exact ⟨hB, hInj⟩
  map_func := by
    intro n F xs z hz
    rw [act.onFunc_one]
    change z ∈ (A.pushforwardAlong q).func F (q ∘ xs)
    exact ⟨xs, rfl, hz⟩

/-- The *first* factor A→U in the controlled saturation is
a genuine Γ-homomorphism-embedding as soon as the quotient
function fibres satisfy exact congruence. Both injectivity
and relation reflection hold locally on each irreducible
closed piece, and all set-valued function fibres match. -/
theorem toSafeRelationSaturation_isHomomorphismEmbedding
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q)
    (hCompat : A.FunctionFibresCompatible q) :
    IsHomomorphismEmbedding act
      (toSafeRelationSaturation act f hf q g hFactor hCompat) := by
  intro S hS hIrr
  refine ⟨?_, ?_, ?_⟩
  · exact f.factor_injOn_of_homomorphismEmbedding
      act hf q g hFactor S hS hIrr
  · intro n R xs hxs
    change (safeRelationSaturation act A q B g f.lang).rel
      (act.onRel (1 : Γ) R) (q ∘ xs) ↔ A.rel R xs
    rw [act.onRel_one]
    constructor
    · intro hNew
      have hB : B.rel (act.onRel f.lang R)
          (f.toFun ∘ xs) := by
        have hb : B.rel (act.onRel f.lang R)
            (g ∘ (q ∘ xs)) := hNew.1
        simpa only [hFactor, Function.comp_assoc] using hb
      exact ((hf S hS hIrr).2.1 R xs hxs).mp hB
    · intro hOld
      exact (toSafeRelationSaturation act f hf q g
        hFactor hCompat).map_rel R xs hOld
  · intro n F xs hxs
    change imageSet q (A.func F xs) =
      (A.pushforwardAlong q).func F (q ∘ xs)
    exact A.pushforward_func_eq_of_compatible
      q hCompat F xs

end Homomorphism
end Structure
end AllThoseEPPA
