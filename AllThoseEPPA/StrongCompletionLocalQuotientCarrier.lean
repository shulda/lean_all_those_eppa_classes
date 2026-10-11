import AllThoseEPPA.StrongCompletionLocalCollapse

/-!
# Finite intermediate carrier for a local closure collapse

Take a noninjective Γ-homomorphism-embedding f:A→B and a
chosen collided pair a≠b. The preceding module constructed a
vertex map c:V→V collapsing exactly the matching right-hand
closure onto the left, preserving f everywhere.

Here we make its **actual finite image** the intermediate
vertex type U and construct the two maps

    q : V ↠ U,       g : U → W,

satisfying f = g ∘ q. The first map is surjective but
noninjective; the image type is finite whenever V is.

This is a bona fide finite set-level factorization, with
no chosen representatives or cardinality restrictions on W.
Defining a Γ-structure on U for which q and g are BOTH
homomorphism-embeddings remains the central open obligation
in Proposition 11.3. Neither property is assumed here.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

/-- The intermediate carrier is exactly the image of the
closure-collapse map. -/
def localCollapseCarrier
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) : Type w :=
  Set.range (f.collapseRightClosure act hf hab)

/-- The quotient's underlying map is the normalization
with codomain restricted to its actual image. -/
noncomputable def localCollapseToCarrier
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) :
    V → f.localCollapseCarrier act hf hab :=
  fun x => ⟨f.collapseRightClosure act hf hab x, ⟨x, rfl⟩⟩

/-- The quotient vertex map is surjective by its codomain
being defined as the range. -/
theorem localCollapseToCarrier_surjective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) :
    Function.Surjective (f.localCollapseToCarrier act hf hab) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, hx⟩ := hz
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- The intermediate vertex carrier remains finite if the
source carrier was finite. -/
theorem localCollapseCarrier_finite
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    [Finite V]
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) :
    Finite (f.localCollapseCarrier act hf hab) :=
  Finite.of_surjective
    (f.localCollapseToCarrier act hf hab)
    (f.localCollapseToCarrier_surjective act hf hab)

/-- The first factor is genuinely noninjective; in particular
the intermediate carrier has fewer vertices than the source
when both are finite. -/
theorem localCollapseToCarrier_not_injective
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hne : a ≠ b) (hab : f a = f b) :
    ¬ Function.Injective (f.localCollapseToCarrier act hf hab) := by
  intro hInj
  apply f.collapseRightClosure_not_injective act hf hne hab
  intro x y hxy
  apply hInj
  apply Subtype.ext
  exact hxy

/-- A well-defined second vertex map to the original target:
each intermediate representative is itself a source vertex. -/
noncomputable def localCollapseDescent
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) :
    f.localCollapseCarrier act hf hab → W :=
  fun z => f z.1

/-- The two vertex maps really compose to f on every point. -/
theorem localCollapseDescent_comp
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    (f : Homomorphism act A B)
    (hf : IsHomomorphismEmbedding act f)
    {a b : V} (hab : f a = f b) :
    f.toFun =
      (f.localCollapseDescent act hf hab) ∘
        (f.localCollapseToCarrier act hf hab) := by
  funext x
  exact (f.collapseRightClosure_preserves_f act hf hab x).symm

end Homomorphism
end Structure
end AllThoseEPPA
