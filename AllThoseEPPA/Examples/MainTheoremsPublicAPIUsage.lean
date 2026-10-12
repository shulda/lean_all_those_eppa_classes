import AllThoseEPPA.MainTheorems

/-!
# Consumer smoke tests of the general main-theorem API

Every theorem below imports ONLY `AllThoseEPPA.MainTheorems`.
They destruct the public outputs or apply a public theorem to a
concrete mathematical goal, and are compiled by the root
`AllThoseEPPA` target and its CI axiom audit.
-/

namespace AllThoseEPPA.MainTheorems.APIUsage

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- Extract ordinary EPPA and faithfulness from the unrestricted,
coherent witness, starting with only `[Finite α]`. -/
theorem unrestrictedYieldsOrdinary
    {α : Type v} [Finite α]
    (act : L.Action Γ) (A : Structure L α)
    (hOrbit : A.HasFiniteRelabelOrbit act) :
    ∃ (β : Type (max u v)) (_ : Finite β)
      (B : Structure L β) (ι : Structure.Embedding act A B),
      Structure.IsEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι := by
  obtain ⟨β, hβ, B, ι, ⟨c⟩, hFaith⟩ :=
    MainTheorems.unrestrictedFaithfulCoherentEPPA act A hOrbit
  exact ⟨β, hβ, B, ι, c.isEPPAWitness act, hFaith⟩

/-- Extract both the restricted witness's faithfulness and its
conditional transfer of coherent EPPA, without opening any of the
internal proof-construction modules. -/
theorem restrictedPreservesCoherence
    {α β : Type (max u v)} [Finite α] [Finite β]
    (act : L.Action Γ)
    (A : Structure L α) (B₀ : Structure L β)
    (ψ : Structure.Embedding act A B₀)
    (hCoh : Structure.IsCoherentEPPAWitness act ψ)
    (n : ℕ) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
      (B : Structure L δ) (ι : Structure.Embedding act A B),
      Structure.IsCoherentEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι := by
  obtain ⟨c⟩ := hCoh
  obtain ⟨δ, hδ, B, ι, _hE, hFaith, _hProjection, _hTrees, hTransfer⟩ :=
    MainTheorems.restrictedLocallyTreeLikeEPPA
      act A B₀ ψ (c.isEPPAWitness act) n
  exact ⟨δ, hδ, B, ι, hTransfer ⟨c⟩, hFaith⟩

/-- A consumer of the forbidden-family conclusion: extract an
actual finite Forb(F)-witness, retaining coherence. -/
theorem herwigLascarRetainsForbiddenClass
    {α : Type (max u v)} [Finite α]
    {M : Type x}
    (F : HerwigLascar.FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (A : Structure L α)
    (hOrbit : A.HasFiniteRelabelOrbit act)
    (N : Structure L M)
    (a : Structure.Embedding act A N)
    (hExt : Structure.IsEPPAWitness act a)
    (hN : F.Avoids act N) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
      (B : Structure L δ), F.Avoids act B := by
  obtain ⟨δ, hδ, B, _ι, _hCoh, _hFaith, hAvoid⟩ :=
    MainTheorems.herwigLascar F act A hOrbit N a hExt hN
  exact ⟨δ, hδ, B, hAvoid⟩

/-- Consume the class-level ordinary transfer by requesting an
individual EPPA witness for A in K. -/
theorem locallyFiniteClassWitness
    (act : L.Action Γ)
    (K : TreeLike.HereditaryFiniteStrongAmalgamationClass act)
    (E : {V : Type (max u v)} → Structure L V → Prop)
    (hSub :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        K.toAmalgamationClass.mem A → E A)
    (hE : TreeLike.FiniteClassHasEPPA act E)
    (hIrr :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        K.toAmalgamationClass.mem A → A.IsIrreducible)
    (hLocallyFinite :
      ∀ {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.toAmalgamationClass.mem A → E B₀ →
          TreeLike.HasLocallyFiniteAutomorphismPreservingCompletion
            act A B₀ K.toAmalgamationClass)
    {α : Type (max u v)} [Finite α]
    (A : Structure L α) (hA : K.toAmalgamationClass.mem A) :
    ∃ (β : Type (max u v)) (_ : Finite β)
      (B : Structure L β) (ι : Structure.Embedding act A B),
      K.toAmalgamationClass.mem B ∧
      Structure.IsEPPAWitness act ι := by
  exact (MainTheorems.locallyFiniteEPPA
    act K E hSub hE hIrr hLocallyFinite) A hA

/-- Use Proposition 11.3 without requiring an automorphism lift. -/
theorem completionUpgrade
    (act : L.Action Γ)
    (K : TreeLike.HereditaryFiniteStrongAmalgamationClass act)
    {V : Type v} [Finite V] (A : Structure L V)
    (h : K.toAmalgamationClass.HasCompletion A) :
    K.toAmalgamationClass.HasStrongCompletion A := by
  exact (MainTheorems.completionIffStrong act K A).mp h

-- Coherent class transfer is available from this SAME public import:
#check MainTheorems.locallyFiniteCoherentEPPA

end AllThoseEPPA.MainTheorems.APIUsage
