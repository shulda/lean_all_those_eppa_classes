import AllThoseEPPA.StrongCompletionLocallyFiniteClassTheorem

/-!
# Manuscript Theorem 1.6: ambient-class / subclass interface

The immediately preceding theorem receives finite EPPA-witnesses
in the ambient class E through an existential interface. This file
replaces that interface with the usual two mathematical assumptions:

* E has ordinary (respectively coherent) EPPA;
* every finite member of K also belongs to E.

The rest of the proof invokes the checked locally finite
construction verbatim. This isolates the manuscript's precise
subclass conclusion from the technically stronger version in the
preceding file. Heredity of K and its strong amalgamation property
may be used to *instantiate* our finite amalgamation interface,
but are not additionally needed by the proof after that interface
has been supplied.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- Ordinary EPPA of an ambient finite class. -/
def FiniteClassHasEPPA
    (act : L.Action Γ)
    (E : {V : Type (max u v)} → Structure L V → Prop) : Prop :=
  ∀ {α : Type (max u v)} [Finite α]
    (A : Structure L α), E A →
      ∃ (β : Type (max u v)) (_ : Finite β)
          (B : Structure L β)
          (ι : Structure.Embedding act A B),
        E B ∧ Structure.IsEPPAWitness act ι

/-- Coherent EPPA of an ambient finite class. -/
def FiniteClassHasCoherentEPPA
    (act : L.Action Γ)
    (E : {V : Type (max u v)} → Structure L V → Prop) : Prop :=
  ∀ {α : Type (max u v)} [Finite α]
    (A : Structure L α), E A →
      ∃ (β : Type (max u v)) (_ : Finite β)
          (B : Structure L β)
          (ι : Structure.Embedding act A B),
        E B ∧ Structure.IsCoherentEPPAWitness act ι

/-- The ordinary EPPA assertion of manuscript Theorem 1.6
in class/subclass terminology.

Under the locally finite automorphism-preserving condition,
an amalgamation subclass K of an ambient EPPA class E,
consisting of irreducible finite Γ-structures, has EPPA. -/
theorem locallyFiniteSubclass_hasEPPA
    (act : L.Action Γ)
    (K : FiniteAmalgamationClass act)
    (E : {V : Type (max u v)} → Structure L V → Prop)
    (hSub :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α), K.mem A → E A)
    (hE : FiniteClassHasEPPA act E)
    (hIrr :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α), K.mem A → A.IsIrreducible)
    (hLocallyFinite :
      ∀ {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.mem A → E B₀ →
          HasLocallyFiniteAutomorphismPreservingCompletion
            act A B₀ K) :
    K.HasEPPA := by
  apply locallyFiniteClass_hasEPPA act K E hIrr
  · intro α hα A hKA
    exact hE A (hSub A hKA)
  · exact hLocallyFinite

/-- Coherent version of the class transfer, requiring coherent
EPPA only in the ambient class E, not separately in K. -/
theorem locallyFiniteSubclass_hasCoherentEPPA
    (act : L.Action Γ)
    (K : FiniteAmalgamationClass act)
    (E : {V : Type (max u v)} → Structure L V → Prop)
    (hSub :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α), K.mem A → E A)
    (hE : FiniteClassHasCoherentEPPA act E)
    (hIrr :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α), K.mem A → A.IsIrreducible)
    (hLocallyFinite :
      ∀ {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.mem A → E B₀ →
          HasLocallyFiniteAutomorphismPreservingCompletion
            act A B₀ K) :
    K.HasCoherentEPPA := by
  apply locallyFiniteClass_hasCoherentEPPA act K E hIrr
  · intro α hα A hKA
    exact hE A (hSub A hKA)
  · exact hLocallyFinite

end TreeLike
end AllThoseEPPA
