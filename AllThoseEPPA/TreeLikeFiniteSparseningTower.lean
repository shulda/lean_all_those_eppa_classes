import AllThoseEPPA.CycleSparseningTheorem
import AllThoseEPPA.TreeLikeClosedProjection

/-!
# An actual finite tower of cycle-sparsening EPPA witnesses

The proof of manuscript Theorem `thm:maintree` applies Lemma
`lem:sparsen` many times, not just once. Here we package an
actual stage together with its carrier, finite proof, distinguished
embedding of A, ordinary EPPA, and irreducible-structure faithfulness.

The one-step successor is the **concrete cycle-sparsening
construction** already verified in `CycleSparseningTheorem`.
Iterating it produces a genuine finite tower of EPPA witnesses;
there is no existentially chosen or assumed successor.

We also expose the actual homomorphism-embedding from the new
stage to the preceding stage, and its exact equality of
set-valued unary function fibres. This is the map used to
project a small closed induced substructure backwards.

Coherence is an optional invariant: if the starting stage has
coherent EPPA, each successor and every iterated stage inherits
it by the previously checked coherent sparsening lift.

What remains for `thm:maintree` is to iterate closed subsets
through these typed projections, apply the rank argument,
compose partial homomorphism-embeddings on irreducibles,
and handle the extra distinguished relation E and the reduct.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w
variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]
variable {α : Type (max u v)}

/-- An actual finite, irreducible-structure faithful EPPA
witness for a fixed A and fixed language action, with an
explicit distinguished embedding. All carrier types are in
one stable universe so the concrete sparsening construction
can be iterated. -/
structure FaithfulSparseningStage
    (act : L.Action Γ) (A : Structure L α) where
  Carrier : Type (max u v)
  finiteCarrier : Finite Carrier
  model : Structure L Carrier
  embedding : Structure.Embedding act A model
  isEPPA : Structure.IsEPPAWitness act embedding
  isFaithful : Structure.IsIrreducibleStructureFaithful act embedding

namespace FaithfulSparseningStage

/-- Package a specific existing finite faithful EPPA witness
as the initial member of the tower. -/
def initial
    (act : L.Action Γ) (A : Structure L α)
    {β : Type (max u v)} [Finite β]
    (B : Structure L β)
    (ψ : Structure.Embedding act A B)
    (heppa : Structure.IsEPPAWitness act ψ)
    (hfaith : Structure.IsIrreducibleStructureFaithful act ψ) :
    FaithfulSparseningStage act A where
  Carrier := β
  finiteCarrier := inferInstance
  model := B
  embedding := ψ
  isEPPA := heppa
  isFaithful := hfaith

/-- One actual cycle-sparsening step preserves finite
carrier, EPPA and irreducible-structure faithfulness,
and returns the concrete new witness with its canonical
embedding of the same original A. -/
noncomputable def next
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) :
    FaithfulSparseningStage act A := by
  letI : Finite s.Carrier := s.finiteCarrier
  exact
    { Carrier := Sparsening.WitnessVertex s.model E
      finiteCarrier := Sparsening.witnessVertex_finite s.model E
      model := Sparsening.witnessStructure s.model E
      embedding := Sparsening.canonicalEmbedding
        act A s.model s.embedding E hfix hcomplete
      isEPPA := Sparsening.sparseningWitness_isEPPAWitness
        act A s.model s.embedding E hfix hcomplete s.isEPPA
      isFaithful :=
        Sparsening.sparseningWitness_isIrreducibleStructureFaithful
          act A s.model s.embedding E hfix hcomplete s.isFaithful }

/-- The exact homomorphism-embedding of the next
cycle-sparsening stage onto the immediately preceding stage.
Its vertex map is the previously checked coordinate
projection, not an arbitrary homomorphism. -/
noncomputable def nextProjection
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) :
    Structure.Homomorphism act
      (s.next act A E hfix hcomplete).model s.model :=
  Sparsening.projection act s.model E

/-- Every interstage projection preserves the embedding
property on all irreducible induced substructures. -/
theorem nextProjection_isHomomorphismEmbedding
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) :
    Structure.Homomorphism.IsHomomorphismEmbedding act
      (s.nextProjection act A E hfix hcomplete) :=
  Sparsening.projection_isHomomorphismEmbedding act s.model E

/-- Each tower projection maps complete unary function
fibres **onto** the previous stage's fibres, by equality.
This is what lets the backwards image of a closed small
substructure remain closed. -/
theorem nextProjection_exact_functions
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    {n : ℕ} (F : L.FuncSymbol n)
    (xs : Fin n → (s.next act A E hfix hcomplete).Carrier) :
    Structure.imageSet
        (s.nextProjection act A E hfix hcomplete).toFun
        ((s.next act A E hfix hcomplete).model.func F xs) =
      s.model.func
        (act.onFunc (s.nextProjection act A E hfix hcomplete).lang F)
        ((s.nextProjection act A E hfix hcomplete).toFun ∘ xs) :=
  Sparsening.projection_map_func_eq act s.model E F xs

/-- Apply the actual sparsening successor k times.
Unlike an abstract existence tower, this has an explicit
well-typed finite witness and distinguished embedding at
**every** level. -/
noncomputable def iterate
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) :
    ℕ → FaithfulSparseningStage act A
  | 0 => s
  | k + 1 =>
      (iterate act A E hfix hcomplete s k).next
        act A E hfix hcomplete

/-- The projection from level k+1 to level k in the
explicit finite sparsening tower. -/
noncomputable def iterateProjection
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A) (k : ℕ) :
    Structure.Homomorphism act
      (iterate act A E hfix hcomplete s (k+1)).model
      (iterate act A E hfix hcomplete s k).model :=
  (iterate act A E hfix hcomplete s k).nextProjection
    act A E hfix hcomplete

/-- Coherent EPPA, if present initially, survives the
specific concrete sparsening successor step. -/
theorem next_coherent
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (hcoh : Structure.IsCoherentEPPAWitness act s.embedding) :
    Structure.IsCoherentEPPAWitness act
      (s.next act A E hfix hcomplete).embedding := by
  letI : Finite s.Carrier := s.finiteCarrier
  exact Sparsening.sparseningWitness_isCoherentEPPAWitness
    act A s.model s.embedding E hfix hcomplete hcoh

/-- Coherent EPPA is preserved at *every level* of the
actual dependent tower, by ordinary induction on the
number of sparsening steps. -/
theorem iterate_coherent
    (act : L.Action Γ) (A : Structure L α)
    (E : L.RelSymbol 2)
    (hfix : act.FixesRel E)
    (hcomplete : A.EdgeComplete E)
    (s : FaithfulSparseningStage act A)
    (hcoh : Structure.IsCoherentEPPAWitness act s.embedding)
    (k : ℕ) :
    Structure.IsCoherentEPPAWitness act
      (iterate act A E hfix hcomplete s k).embedding := by
  induction k with
  | zero => exact hcoh
  | succ k ih =>
      exact next_coherent act A E hfix hcomplete
        (iterate act A E hfix hcomplete s k) ih

end FaithfulSparseningStage
end TreeLike
end AllThoseEPPA
