import AllThoseEPPA.StrongCompletionPushforward

/-!
# Relation saturation restricted to injective primitive closures

The naive existential pushforward of a Γ-structure along q
does not necessarily make the descended map g a
homomorphism-embedding. Saturating **all** relation tuples
from the target B is also unsafe: it can introduce new
irreducibles containing two vertices with the same g-value.

We define a controlled intermediate structure, using the
same exact set-valued function fibres as q₊A but adding
a relation tuple only when

1. its g-image satisfies the corresponding relation in B;
2. g is injective on the **functionally generated closure**
   of the entire tuple in the intermediate structure.

The second requirement prevents the tuple itself from
creating a primitive irreducible piece on which g collapses
two vertices.

In this module we prove only the unconditional structural
interfaces: the precise relation criterion, equality of
function fibres and closure operators with q₊A, and the
fact that g is a genuine Γ-homomorphism from the controlled
saturation into B whenever the original f:A→B factors
through q on vertices.

Further work must prove that q remains locally exact on
source irreducibles and that g is injective on *all*
irreducibles of the saturated structure. No such claims
are built into this definition.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {U : Type x} {W : Type y}

/-- Controlled saturation of the existential pushforward.
Function fibres are those of the canonical q-pushforward;
relations are pulled back from B only where the generated
function closure has a g-injective image. -/
def safeRelationSaturation
    (act : L.Action Γ)
    (A : Structure L V) (q : V → U)
    (B : Structure L W) (g : U → W)
    (lang : Γ) :
    Structure L U where
  rel := by
    intro n R xs
    exact B.rel (act.onRel lang R) (g ∘ xs) ∧
      Set.InjOn g ((A.pushforwardAlong q).closureSet (Set.range xs))
  func := (A.pushforwardAlong q).func

/-- The function fibres of controlled saturation are
*definitionally* those of the canonical existential pushforward. -/
theorem safeRelationSaturation_func
    (act : L.Action Γ)
    (A : Structure L V) (q : V → U)
    (B : Structure L W) (g : U → W) (lang : Γ)
    {n : ℕ} (F : L.FuncSymbol n) (xs : Fin n → U) :
    (safeRelationSaturation act A q B g lang).func F xs =
      (A.pushforwardAlong q).func F xs := rfl

/-- The functionally generated closures are unchanged when
relation saturation is introduced. This permits all
one-point and relation-tuple closure calculations to use
the simpler existential pushforward. -/
theorem safeRelationSaturation_closureSet
    (act : L.Action Γ)
    (A : Structure L V) (q : V → U)
    (B : Structure L W) (g : U → W) (lang : Γ)
    (S : Set U) :
    (safeRelationSaturation act A q B g lang).closureSet S =
      (A.pushforwardAlong q).closureSet S := rfl

/-- On any tuple whose generated function closure is
g-injective, controlled saturation reflects the target
relation **exactly**. -/
theorem safeRelationSaturation_rel_iff
    (act : L.Action Γ)
    (A : Structure L V) (q : V → U)
    (B : Structure L W) (g : U → W) (lang : Γ)
    {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → U)
    (hInj :
      Set.InjOn g ((A.pushforwardAlong q).closureSet (Set.range xs))) :
    (safeRelationSaturation act A q B g lang).rel R xs ↔
      B.rel (act.onRel lang R) (g ∘ xs) := by
  change (B.rel (act.onRel lang R) (g ∘ xs) ∧
    Set.InjOn g ((A.pushforwardAlong q).closureSet (Set.range xs))) ↔
      B.rel (act.onRel lang R) (g ∘ xs)
  exact and_iff_left hInj

namespace Homomorphism

/-- The descended map is always a Γ-**homomorphism**
from the controlled saturation into B. Its language
component is exactly f.lang, and its point map is g.

The fact that this is a *homomorphism-embedding* requires
additional arguments beyond this theorem. -/
def fromSafeRelationSaturation
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (q : V → U) (g : U → W)
    (hFactor : f.toFun = g ∘ q) :
    Homomorphism act
      (safeRelationSaturation act A q B g f.lang) B where
  lang := f.lang
  toFun := g
  map_rel := by
    intro n R xs hRel
    exact hRel.1
  map_func := (fromPushforward act f q g hFactor).map_func

end Homomorphism
end Structure
end AllThoseEPPA
