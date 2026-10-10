import AllThoseEPPA.StrongCompletionLocallyFiniteStep

/-!
# Class-level EPPA theorem for locally finite subclasses

This is the class-level packaging of the exact manuscript
Theorem 1.6 implication, with hypotheses factored explicitly.

For each finite irreducible A in K we require:
* a finite starting EPPA witness B₀ in an ambient class E;
* ordinary locally bounded completions of small substructures
  of relevant witness candidates, as in Definition 11.2;
* a composition-preserving automorphism lift from the resulting
  strong completion of the candidate.

The finite amalgamation-class interface supplies Observation 9.4.
Nothing in this derivation requires Proposition 11.3, since
Definition 11.2 itself asks only for ordinary completions of
small substructures. The corollary is valid under the manuscript's
stronger hereditary/SAP hypotheses as well.

This theorem deliberately does NOT assert that the output
completion is irreducible-structure faithful: that property is
not part of the manuscript's Theorem 1.6 conclusion and need
not survive adding relations in the completion.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- The finite-class Γ-EPPA property on all finite carrier types
in the selected universe. -/
def FiniteAmalgamationClass.HasEPPA
    (act : L.Action Γ)
    (K : FiniteAmalgamationClass act) : Prop :=
  ∀ {α : Type (max u v)} [Finite α]
    (A : Structure L α), K.mem A →
      ∃ (β : Type (max u v)) (_ : Finite β)
          (B : Structure L β)
          (ι : Structure.Embedding act A B),
        K.mem B ∧ Structure.IsEPPAWitness act ι

/-- Coherent version of the finite-class Γ-EPPA property. -/
def FiniteAmalgamationClass.HasCoherentEPPA
    (act : L.Action Γ)
    (K : FiniteAmalgamationClass act) : Prop :=
  ∀ {α : Type (max u v)} [Finite α]
    (A : Structure L α), K.mem A →
      ∃ (β : Type (max u v)) (_ : Finite β)
          (B : Structure L β)
          (ι : Structure.Embedding act A B),
        K.mem B ∧ Structure.IsCoherentEPPAWitness act ι

/-- Ordinary EPPA transfers from E to K under the locally finite
automorphism-preserving condition of Definition 11.2.

The hInitial argument explicitly supplies finite ambient-class
EPPA witnesses; this is precisely the component obtained by
assuming E has EPPA and K is a subclass of E. -/
theorem locallyFiniteClass_hasEPPA
    (act : L.Action Γ)
    (K : FiniteAmalgamationClass act)
    (E : {V : Type (max u v)} → Structure L V → Prop)
    (hIrreducible :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α), K.mem A → A.IsIrreducible)
    (hInitial :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α), K.mem A →
          ∃ (β : Type (max u v)) (_ : Finite β)
              (B₀ : Structure L β)
              (ψ : Structure.Embedding act A B₀),
            E B₀ ∧ Structure.IsEPPAWitness act ψ)
    (hLocallyFinite :
      ∀ {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.mem A → E B₀ →
          HasLocallyFiniteAutomorphismPreservingCompletion
            act A B₀ K) :
    K.HasEPPA act := by
  intro α hα A hKA
  obtain ⟨β, hβ, B₀, ψ, hE, hEPPA₀⟩ :=
    hInitial A hKA
  letI : Finite β := hβ
  obtain ⟨Z, hZ, B, ι, hKB, hEPPA, _⟩ :=
    restrictedEPPA_inLocallyFiniteClass
      act A (hIrreducible A hKA) K hKA
      B₀ ψ hEPPA₀ (hLocallyFinite A B₀ hKA hE)
  exact ⟨Z, hZ, B, ι, hKB, hEPPA⟩

/-- If the starting ambient witnesses are coherent, the same
locally finite argument transfers the *coherent* EPPA property.
No additional coherent local completion is assumed: the
automorphism-preserving lift ensures coherence automatically. -/
theorem locallyFiniteClass_hasCoherentEPPA
    (act : L.Action Γ)
    (K : FiniteAmalgamationClass act)
    (E : {V : Type (max u v)} → Structure L V → Prop)
    (hIrreducible :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α), K.mem A → A.IsIrreducible)
    (hInitial :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α), K.mem A →
          ∃ (β : Type (max u v)) (_ : Finite β)
              (B₀ : Structure L β)
              (ψ : Structure.Embedding act A B₀),
            E B₀ ∧ Structure.IsCoherentEPPAWitness act ψ)
    (hLocallyFinite :
      ∀ {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.mem A → E B₀ →
          HasLocallyFiniteAutomorphismPreservingCompletion
            act A B₀ K) :
    K.HasCoherentEPPA act := by
  intro α hα A hKA
  obtain ⟨β, hβ, B₀, ψ, hE, ⟨c⟩⟩ :=
    hInitial A hKA
  letI : Finite β := hβ
  have hEPPA₀ : Structure.IsEPPAWitness act ψ :=
    c.isEPPAWitness act
  obtain ⟨Z, hZ, B, ι, hKB, _hEPPA, hCoherent⟩ :=
    restrictedEPPA_inLocallyFiniteClass
      act A (hIrreducible A hKA) K hKA
      B₀ ψ hEPPA₀ (hLocallyFinite A B₀ hKA hE)
  exact ⟨Z, hZ, B, ι, hKB, hCoherent ⟨c⟩⟩

end TreeLike
end AllThoseEPPA
