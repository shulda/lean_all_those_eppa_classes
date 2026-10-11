import AllThoseEPPA.StrongCompletionManuscriptSubclass

/-!
# Strong amalgamation and hereditary subclasses

The actual manuscript Theorem 1.6 assumes a hereditary subclass K
of finite irreducible structures with **strong** amalgamation.
The core formalized argument needs only the weaker amalgamation
operation recorded by FiniteAmalgamationClass.

This module supplies an explicit *strong* Γ-amalgamation interface
including the exact intersection condition, as well as heredity and
finiteness of members, then forgets only the extra assumptions to
invoke the core class theorem. Thus the paper's stronger, familiar
hypothesis becomes a literal special case of the Lean theorem,
instead of an informal comment about amalgamation.

The hereditary property is expressed under exact Γ-embeddings,
so an interface embedded in a class member also belongs to the class.
The strong intersection condition says that if j₁(x)=j₂(y),
then both points arise from the specified interface,
in addition to equality of the Γ-embedding maps on that interface.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- A hereditary class of finite Γ-structures with strong
amalgamation. The sources of amalgamation may have different
carrier types; symbols may be permuted by the group Γ. -/
structure HereditaryFiniteStrongAmalgamationClass
    (act : L.Action Γ) where
  mem : {V : Type v} → Structure L V → Prop
  finite_of_mem :
    ∀ {V : Type v} (B : Structure L V),
      mem B → Finite V
  hereditary :
    ∀ {V W : Type v} {D : Structure L V}
      {B : Structure L W}
      (e : Structure.Embedding act D B),
      mem B → mem D
  strong_amalgamate :
    ∀ {I X Y : Type v}
      {D : Structure L I} {B₁ : Structure L X}
      {B₂ : Structure L Y}
      (f : Structure.Embedding act D B₁)
      (g : Structure.Embedding act D B₂),
      mem D → mem B₁ → mem B₂ →
      ∃ (Z : Type v) (_ : Finite Z) (B : Structure L Z),
        mem B ∧
        ∃ (j₁ : Structure.Embedding act B₁ B)
          (j₂ : Structure.Embedding act B₂ B),
          j₁.comp f = j₂.comp g ∧
          (∀ (x : X) (y : Y),
            j₁ x = j₂ y →
              ∃ i : I, f i = x ∧ g i = y)

namespace HereditaryFiniteStrongAmalgamationClass

/-- An exact Γ-strong amalgamation supplies an ordinary
amalgamation class by forgetting only the range-overlap
certificate. No extra combinatorial argument is needed. -/
def toAmalgamationClass
    {act : L.Action Γ}
    (K : HereditaryFiniteStrongAmalgamationClass act) :
    FiniteAmalgamationClass act where
  mem := K.mem
  amalgamate := by
    intro I X Y D B₁ B₂ f g hB₁ hB₂
    have hD : K.mem D := K.hereditary f hB₁
    obtain ⟨Z, hZ, B, hB, j₁, j₂, hCommute, _hStrong⟩ :=
      K.strong_amalgamate f g hD hB₁ hB₂
    exact ⟨Z, hZ, B, hB, j₁, j₂, hCommute⟩

/-- Ordinary EPPA in the **actual hereditary strong-amalgamation
setting** of the manuscript, using its local finiteness
automorphism-preserving completion condition. -/
theorem locallyFiniteSubclass_hasEPPA
    (act : L.Action Γ)
    (K : HereditaryFiniteStrongAmalgamationClass act)
    (E : {V : Type (max u v)} → Structure L V → Prop)
    (hSub :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        K.toAmalgamationClass.mem A → E A)
    (hE : FiniteClassHasEPPA act E)
    (hIrr :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        K.toAmalgamationClass.mem A → A.IsIrreducible)
    (hLocallyFinite :
      ∀ {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.toAmalgamationClass.mem A → E B₀ →
          HasLocallyFiniteAutomorphismPreservingCompletion
            act A B₀ K.toAmalgamationClass) :
    K.toAmalgamationClass.HasEPPA := by
  exact TreeLike.locallyFiniteSubclass_hasEPPA
    act K.toAmalgamationClass E hSub hE hIrr hLocallyFinite

/-- If the ambient class has coherent EPPA then this
hereditary strong-amalgamation subclass has coherent EPPA. -/
theorem locallyFiniteSubclass_hasCoherentEPPA
    (act : L.Action Γ)
    (K : HereditaryFiniteStrongAmalgamationClass act)
    (E : {V : Type (max u v)} → Structure L V → Prop)
    (hSub :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        K.toAmalgamationClass.mem A → E A)
    (hE : FiniteClassHasCoherentEPPA act E)
    (hIrr :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        K.toAmalgamationClass.mem A → A.IsIrreducible)
    (hLocallyFinite :
      ∀ {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.toAmalgamationClass.mem A → E B₀ →
          HasLocallyFiniteAutomorphismPreservingCompletion
            act A B₀ K.toAmalgamationClass) :
    K.toAmalgamationClass.HasCoherentEPPA := by
  exact TreeLike.locallyFiniteSubclass_hasCoherentEPPA
    act K.toAmalgamationClass E hSub hE hIrr hLocallyFinite

end HereditaryFiniteStrongAmalgamationClass
end TreeLike
end AllThoseEPPA
