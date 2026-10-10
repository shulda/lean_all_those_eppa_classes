import AllThoseEPPA.HerwigLascarCompleteEObstruction
import AllThoseEPPA.UnrestrictedFaithfulEPPA

/-!
# Herwig--Lascar EPPA theorem for finite forbidden families

A finite A with finite Γ-relabel orbit sits inside an arbitrary
(possibly infinite) N avoiding a finite heterogeneous forbidden
family F. If every partial automorphism of A extends to an
automorphism of N, then A has a finite coherent, irreducible-
structure-faithful EPPA witness B that also avoids F.

The genuine proof combines four previously checked constructions:
unrestricted coherent EPPA, the complete-E tree-like refinement,
the infinitecopies lemma, and the finite-forbidden-image argument.
The ambient N is never assumed to be finite. Its exclusion of
homomorphism-embeddings of members of F is the essential
Herwig--Lascar hypothesis.
-/

namespace AllThoseEPPA
namespace HerwigLascar

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)} [Finite α]
variable {M : Type x}

/-- Manuscript `thm:main`: Herwig--Lascar extension-closure of
Forb(F) under finite (coherent and faithful) EPPA witnesses.
The forbidden family may be empty, and its members have
different finite carrier types. Γ may act nontrivially on
language symbols. -/
theorem finiteOrbitHerwigLascar
    (F : FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (A : Structure L α)
    (hOrbit : A.HasFiniteRelabelOrbit act)
    (N : Structure L M)
    (a : Structure.Embedding act A N)
    (hExt : Structure.IsEPPAWitness act a)
    (hN : F.Avoids act N) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
        (B : Structure L δ)
        (ι : Structure.Embedding act A B),
      Structure.IsCoherentEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι ∧
      F.Avoids act B := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  obtain ⟨β, hβ, B₀, ψ, ⟨c⟩, _hFaith₀⟩ :=
    Faithful.finiteOrbitUnaryStructuresHaveFaithfulCoherentEPPA
      act A hOrbit
  letI : Finite β := hβ
  have hEPPA₀ : Structure.IsEPPAWitness act ψ :=
    c.isEPPAWitness act
  obtain ⟨δ, hδ, B, ι, _hEPPA, hFaith, hAvoid, hCoh⟩ :=
    restrictedEPPA_avoidingForbidden
      F act A B₀ ψ hEPPA₀ N a hExt hN
  exact ⟨δ, hδ, B, ι, hCoh ⟨c⟩, hFaith, hAvoid⟩

end HerwigLascar
end AllThoseEPPA
