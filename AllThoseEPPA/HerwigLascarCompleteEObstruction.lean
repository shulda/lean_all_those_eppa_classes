import AllThoseEPPA.HerwigLascarForbiddenImage
import AllThoseEPPA.TreeLikeFixedEFullMainTheorem
import AllThoseEPPA.TreeLikeInfiniteCopiesCompleteEReduct
import AllThoseEPPA.TreeLikeFreshBinaryWitnessReduct

/-!
# The complete-E obstruction argument for Herwig--Lascar

Combine the two major completed manuscript results *without*
introducing a second tree construction:

* `thm:maintree`, in its stronger fixed-complete-E form, gives a
  finite witness whose every small closed substructure
  homomorphism-embeds in a literal tree of full A⁺ copies.
* `lem:infinitecopies` places each such tree, after forgetting E,
  by a homomorphism-embedding into any ambient N extending all
  partial automorphisms of A.

The bounded closed-image obstruction principle then proves
that the *reduct* of the finite witness is in Forb(F) whenever N is.
This logic is independent of whether the initial finite EPPA
witness is coherent.
-/

namespace AllThoseEPPA
namespace HerwigLascar

universe u v w x
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α δ β : Type (max u v)} [Finite α]
variable {M : Type x}

/-- The exact avoidance implication from complete-E local trees.
The output expanded structure need not have complete E: E was
sparsified by the locally tree-like construction. -/
theorem avoids_of_localCompleteETrees
    (F : FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (A : Structure L α)
    (N : Structure L M)
    (a : Structure.Embedding act A N)
    (hExt : Structure.IsEPPAWitness act a)
    (Bplus : Structure L.withFixedBinaryRel δ)
    (hSmallPlus :
      ∀ (S : Set δ) (hS : Bplus.IsClosed S),
        S.ncard ≤ F.maxCard →
          ∃ (W : Type (max u v))
              (H : Structure L.withFixedBinaryRel W),
            TreeLike.TreeAmalgamation act.withFixedBinaryRel
              A.withCompleteFixedBinary H ∧
              ∃ f : Structure.Homomorphism act.withFixedBinaryRel
                  (Bplus.induce S hS) H,
                Structure.Homomorphism.IsHomomorphismEmbedding
                  act.withFixedBinaryRel f)
    (hN : F.Avoids act N) :
    F.Avoids act Bplus.forgetFixedBinary := by
  apply F.avoids_of_smallClosedHomEmbeds act
    Bplus.forgetFixedBinary N hN
  intro S hS hBound
  have hSplus : Bplus.IsClosed S := hS
  obtain ⟨W, Hplus, hTree, ⟨fplus, hfplus⟩⟩ :=
    hSmallPlus S hSplus hBound
  obtain ⟨h, hh, _⟩ :=
    TreeLike.completeFreshETree_realizesIntoAmbient
      act A N a hExt Hplus hTree
  refine ⟨h.comp (fplus.forgetFixedBinary act), ?_⟩
  exact Structure.Homomorphism.comp_isHomomorphismEmbedding
    act h (fplus.forgetFixedBinary act) hh
    (Structure.Homomorphism.forgetFixedBinary_isHomomorphismEmbedding
      act fplus hfplus)

/-- From any finite EPPA witness of A, construct a finite
faithful EPPA witness in Forb(F), assuming that some ambient
model in Forb(F) extends every partial automorphism of A.

Coherent EPPA is preserved whenever it was available for the
initial witness. No finiteness assumption on N is used. -/
theorem restrictedEPPA_avoidingForbidden
    (F : FiniteForbiddenFamily.{u,v,(max u v)} L)
    (act : L.Action Γ)
    (A : Structure L α)
    (B₀ : Structure L β) [Finite β]
    (ψ : Structure.Embedding act A B₀)
    (hEPPA : Structure.IsEPPAWitness act ψ)
    (N : Structure L M)
    (a : Structure.Embedding act A N)
    (hExt : Structure.IsEPPAWitness act a)
    (hN : F.Avoids act N) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
        (B : Structure L δ)
        (ι : Structure.Embedding act A B),
      Structure.IsEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι ∧
      F.Avoids act B ∧
      (Structure.IsCoherentEPPAWitness act ψ →
        Structure.IsCoherentEPPAWitness act ι) := by
  classical
  let actPlus : L.withFixedBinaryRel.Action Γ :=
    act.withFixedBinaryRel
  let Aplus : Structure L.withFixedBinaryRel α :=
    A.withCompleteFixedBinary
  let B₀plus : Structure L.withFixedBinaryRel β :=
    B₀.withCompleteFixedBinary
  let ψplus : Structure.Embedding actPlus Aplus B₀plus :=
    ψ.withCompleteFixedBinary act
  have hFix : actPlus.FixesRel
      (Language.withFixedBinaryRel.freshE L) :=
    Language.Action.withFixedBinaryRel_fixesFresh act
  have hComplete : Aplus.EdgeComplete
      (Language.withFixedBinaryRel.freshE L) :=
    Structure.withCompleteFixedBinary_edgeComplete A
  have hEPPAplus : Structure.IsEPPAWitness actPlus ψplus :=
    Structure.isEPPAWitness_withCompleteFixedBinary act ψ hEPPA
  obtain ⟨δ, hδ, Bplus, ιplus, hEPPAout,
      hFaithful, _hProjection, hSmall, hCoh⟩ :=
    TreeLike.fixedE_restrictedEPPA_from_any_witness
      actPlus Aplus (Language.withFixedBinaryRel.freshE L)
      hFix hComplete B₀plus ψplus hEPPAplus F.maxCard
  let B : Structure L δ := Bplus.forgetFixedBinary
  let ι : Structure.Embedding act A B :=
    ιplus.forgetFixedBinary act
  refine ⟨δ, hδ, B, ι, ?_, ?_, ?_, ?_⟩
  · exact
      Structure.isEPPAWitness_forgetFixedBinary_of_complete_source
        act ιplus hEPPAout
  · exact
      Structure.isIrreducibleStructureFaithful_forgetFixedBinary
        act ιplus hFaithful
  · exact avoids_of_localCompleteETrees F act
      A N a hExt Bplus hSmall hN
  · intro hc
    have hcPlus : Structure.IsCoherentEPPAWitness actPlus ψplus :=
      Structure.isCoherentEPPAWitness_withCompleteFixedBinary act ψ hc
    exact
      Structure.isCoherentEPPAWitness_forgetFixedBinary_of_complete_source
        act ιplus (hCoh hcPlus)

end HerwigLascar
end AllThoseEPPA
