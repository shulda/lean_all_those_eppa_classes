import AllThoseEPPA.TreeLikeFreshBinaryEPPA
import AllThoseEPPA.TreeLikeFreshBinaryIrreducibility

/-!
# Forget E while preserving EPPA, coherent EPPA, and irreducible faithfulness

The source of the unrestricted locally tree-like EPPA theorem is a
complete-E expansion of an old-language structure, while the output
witness may carry an arbitrary simple E graph. The old-language
partial automorphisms lift to the complete source, allowing extension
properties to descend from any expanded target.

Irreducibility of an old-language closed induced substructure implies
irreducibility of its expansion. Thus irreducible-structure faithfulness
also descends when the auxiliary relation is forgotten. The arguments
preserve the full Γ-language components and work for genuinely
set-valued functions, without any global injectivity requirement on
homomorphism-embeddings.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x}

namespace Automorphism

/-- Forgetting E commutes with composition of Γ-automorphisms. -/
theorem forgetFixedBinary_comp
    (act : L.Action Γ)
    {B : Structure L.withFixedBinaryRel V}
    (g f : Automorphism act.withFixedBinaryRel B) :
    (g.comp f).forgetFixedBinary act =
      (g.forgetFixedBinary act).comp (f.forgetFixedBinary act) := by
  apply ext_of_lang_apply
  · rfl
  · intro x
    rfl

end Automorphism

/-- An EPPA witness of a *complete* E-expanded source remains an EPPA
witness after forgetting E in both the source and target. The target
is not required to interpret E as complete. -/
theorem isEPPAWitness_forgetFixedBinary_of_complete_source
    (act : L.Action Γ)
    {A : Structure L V}
    {B : Structure L.withFixedBinaryRel W}
    (ψ : Embedding act.withFixedBinaryRel
      A.withCompleteFixedBinary B)
    (hEPPA : IsEPPAWitness act.withFixedBinaryRel ψ) :
    IsEPPAWitness act (ψ.forgetFixedBinary act) := by
  intro p
  obtain ⟨g, hg⟩ := hEPPA (p.withCompleteFixedBinary act)
  exact ⟨g.forgetFixedBinary act, hg⟩

namespace CoherentExtension

/-- Forgetting E in the witness preserves a coherent extension system
provided the *source* E graph was complete. Each old partial
automorphism canonically lifts into the complete expanded source. -/
def forgetFixedBinary_of_complete_source
    (act : L.Action Γ)
    {A : Structure L V}
    {B : Structure L.withFixedBinaryRel W}
    {ψ : Embedding act.withFixedBinaryRel
      A.withCompleteFixedBinary B}
    (h : CoherentExtension act.withFixedBinaryRel ψ) :
    CoherentExtension act (ψ.forgetFixedBinary act) where
  extension := fun p =>
    (h.extension (p.withCompleteFixedBinary act)).forgetFixedBinary act
  extension_spec := by
    intro p
    exact h.extension_spec (p.withCompleteFixedBinary act)
  respects_equivalent := by
    intro p q hpq
    have hEq : PartialIsomorphism.Equivalent
        (p.withCompleteFixedBinary act)
        (q.withCompleteFixedBinary act) := hpq
    exact congrArg (fun g => g.forgetFixedBinary act)
      (h.respects_equivalent
        (p.withCompleteFixedBinary act)
        (q.withCompleteFixedBinary act) hEq)
  coherent := by
    intro f g t ht
    have hTriple : PartialIsomorphism.CoherentTriple
        (f.withCompleteFixedBinary act)
        (g.withCompleteFixedBinary act)
        (t.withCompleteFixedBinary act) := ht
    have hc := h.coherent
      (f.withCompleteFixedBinary act)
      (g.withCompleteFixedBinary act)
      (t.withCompleteFixedBinary act) hTriple
    exact (congrArg (fun z => z.forgetFixedBinary act) hc).trans
      (Automorphism.forgetFixedBinary_comp act
        (h.extension (g.withCompleteFixedBinary act))
        (h.extension (f.withCompleteFixedBinary act)))

end CoherentExtension

/-- Complete-source coherent EPPA also descends along the E-reduct. -/
theorem isCoherentEPPAWitness_forgetFixedBinary_of_complete_source
    (act : L.Action Γ)
    {A : Structure L V}
    {B : Structure L.withFixedBinaryRel W}
    (ψ : Embedding act.withFixedBinaryRel
      A.withCompleteFixedBinary B)
    (h : IsCoherentEPPAWitness act.withFixedBinaryRel ψ) :
    IsCoherentEPPAWitness act (ψ.forgetFixedBinary act) := by
  obtain ⟨c⟩ := h
  exact ⟨c.forgetFixedBinary_of_complete_source act⟩

/-- Irreducible-structure faithfulness descends along deletion of the
fresh E, without any condition on the interpretation of E in A or B.
Irreducibility in the reduct implies irreducibility in the expansion. -/
theorem isIrreducibleStructureFaithful_forgetFixedBinary
    (act : L.Action Γ)
    {A : Structure L.withFixedBinaryRel V}
    {B : Structure L.withFixedBinaryRel W}
    (ψ : Embedding act.withFixedBinaryRel A B)
    (hFaithful : IsIrreducibleStructureFaithful act.withFixedBinaryRel ψ) :
    IsIrreducibleStructureFaithful act (ψ.forgetFixedBinary act) := by
  intro S hS hIrr
  have hOld : ((B.induce S hS).forgetFixedBinary).IsIrreducible := by
    simpa only [forgetFixedBinary_induce] using hIrr
  have hIrrPlus : (B.induce S hS).IsIrreducible :=
    irreducible_of_forgetFixedBinary (B.induce S hS) hOld
  obtain ⟨g, hg⟩ := hFaithful S hS hIrrPlus
  refine ⟨g.forgetFixedBinary act, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hg x hx
  exact ⟨a, ha⟩

end Structure
end AllThoseEPPA
