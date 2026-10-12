import AllThoseEPPA.UnrestrictedFaithfulEPPA
import AllThoseEPPA.TreeLikeUnrestrictedMaintree
import AllThoseEPPA.HerwigLascarTheorem
import AllThoseEPPA.StrongCompletionHereditaryStrongAmalgamation
import AllThoseEPPA.StrongCompletionProposition113API

/-!
# Public API for the main results of All those EPPA classes

**Recommended import for another formalization:**

```lean
import AllThoseEPPA.MainTheorems
```

This file provides stable, named entry points for the general results,
separate from the metric/hypergraph regression examples:

* `MainTheorems.unrestrictedFaithfulCoherentEPPA` (manuscript
  `thm:nreppa`): a finite irreducible-structure faithful,
  **coherent** EPPA witness, assuming finite Γ-relabel orbit.
* `MainTheorems.restrictedLocallyTreeLikeEPPA` (`thm:maintree`):
  refine a given finite EPPA witness, retaining a homomorphism-
  embedding back to the witness, control of all small closed
  substructures by literal trees of full copies of the source,
  and conditional coherent EPPA.
* `MainTheorems.herwigLascar` (`thm:main`): coherent faithful
  finite witness in `Forb(F)`, from a possibly infinite ambient
  structure extending the source partial automorphisms.
* `MainTheorems.locallyFiniteEPPA` and
  `MainTheorems.locallyFiniteCoherentEPPA` (`thm:mainstrong`,
  Theorem 1.6): transfer EPPA to a hereditary finite strong-
  amalgamation subclass under the precise locally finite
  automorphism-preserving completion condition.
* `MainTheorems.completionIffStrong` (Proposition 11.3): the
  related ordinary-versus-injective completion equivalence.

The facade does not silently weaken the hypotheses or introduce
axioms. In particular the restricted theorem needs an initial EPPA
witness, whereas the unrestricted theorem only needs a finite orbit.
All results permit genuine Γ-actions on language symbols and
genuinely set-valued unary functions.

Detailed meanings, dependencies, and consumer examples:
`MAIN_THEOREMS_API.md`.
-/

namespace AllThoseEPPA
namespace MainTheorems

universe u v w x

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type w} [Group Γ]

/-- **Unrestricted coherent, irreducible-structure faithful EPPA**,
manuscript `thm:nreppa`.

In contrast to the original construction-level theorem, the input
requires only `[Finite α]` (not a chosen `Fintype α` enumeration).
All relation arities are allowed; all function symbols must be unary,
and the Γ-relabel orbit of A must be finite. -/
theorem unrestrictedFaithfulCoherentEPPA
    {α : Type v} [Finite α]
    (act : L.Action Γ) (A : Structure L α)
    (hOrbit : A.HasFiniteRelabelOrbit act) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
      (B : Structure L δ) (ι : Structure.Embedding act A B),
      Structure.IsCoherentEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  exact Faithful.finiteOrbitUnaryStructuresHaveFaithfulCoherentEPPA
    act A hOrbit

/-- **Restricted / locally tree-like EPPA**, manuscript
`thm:maintree`.

From a finite existing EPPA witness `ψ : A ↪ B₀` and any bound
`n : ℕ`, produce a new finite witness B. This supplies ordinary
EPPA, irreducible-structure faithfulness, a global homomorphism-
embedding B→B₀, homomorphism-embeddings of every closed
n-small substructure into a literal tree amalgamation of *full*
A-copies, and a proof that coherence of ψ transfers to the output.

The conditional coherent clause does not assert that an arbitrary
ordinary starting witness is automatically coherent. -/
theorem restrictedLocallyTreeLikeEPPA
    {α β : Type (max u v)} [Finite α] [Finite β]
    (act : L.Action Γ)
    (A : Structure L α) (B₀ : Structure L β)
    (ψ : Structure.Embedding act A B₀)
    (hEPPA : Structure.IsEPPAWitness act ψ)
    (n : ℕ) :
    ∃ (δ : Type (max u v)) (_ : Finite δ)
      (B : Structure L δ) (ι : Structure.Embedding act A B),
      Structure.IsEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι ∧
      (∃ f : Structure.Homomorphism act B B₀,
        Structure.Homomorphism.IsHomomorphismEmbedding act f) ∧
      (∀ (S : Set δ) (hS : B.IsClosed S),
        S.ncard ≤ n →
          ∃ (W : Type (max u v)) (H : Structure L W),
            TreeLike.TreeAmalgamation act A H ∧
              ∃ f : Structure.Homomorphism act (B.induce S hS) H,
                Structure.Homomorphism.IsHomomorphismEmbedding act f) ∧
      (Structure.IsCoherentEPPAWitness act ψ →
        Structure.IsCoherentEPPAWitness act ι) := by
  exact TreeLike.restrictedEPPA_from_any_witness
    act A B₀ ψ hEPPA n

/-- **Herwig–Lascar generalisation**, manuscript `thm:main`.

F is a finite family of *finite* forbidden Γ-structures with
possibly different vertex types. `F.Avoids act N` means no member
of F has a Γ-homomorphism-embedding into N. The ambient N may
be infinite, but the source A is finite, has finite Γ-relabel
orbit, embeds in N, and all of its partial automorphisms extend
along that embedding to N.

The finite output B still avoids F and is simultaneously coherent
and irreducible-structure faithful. -/
theorem herwigLascar
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
      (B : Structure L δ) (ι : Structure.Embedding act A B),
      Structure.IsCoherentEPPAWitness act ι ∧
      Structure.IsIrreducibleStructureFaithful act ι ∧
      F.Avoids act B := by
  exact HerwigLascar.finiteOrbitHerwigLascar
    F act A hOrbit N a hExt hN

/-- **Locally finite subclass transfer (ordinary EPPA)**,
manuscript `thm:mainstrong` / Theorem 1.6 in the literal
hereditary strong-amalgamation setting.

The completion assumption is the precise predicate from
Definition 11.2, not a weaker assertion of ordinary local
completion. The ambient E has ordinary EPPA. -/
theorem locallyFiniteEPPA
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
            act A B₀ K.toAmalgamationClass) :
    K.toAmalgamationClass.HasEPPA := by
  exact K.locallyFiniteSubclass_hasEPPA
    act E hSub hE hIrr hLocallyFinite

/-- **Locally finite subclass transfer (coherent EPPA)**,
under the same hereditary strong-amalgamation and local-finiteness
conditions as `locallyFiniteEPPA`.

The ambient E is required to have coherent EPPA. No extra
coherence assumption is imposed on the completions: their
compatible automorphism lifts carry coherent extensions over. -/
theorem locallyFiniteCoherentEPPA
    (act : L.Action Γ)
    (K : TreeLike.HereditaryFiniteStrongAmalgamationClass act)
    (E : {V : Type (max u v)} → Structure L V → Prop)
    (hSub :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        K.toAmalgamationClass.mem A → E A)
    (hE : TreeLike.FiniteClassHasCoherentEPPA act E)
    (hIrr :
      ∀ {α : Type (max u v)} [Finite α]
        (A : Structure L α),
        K.toAmalgamationClass.mem A → A.IsIrreducible)
    (hLocallyFinite :
      ∀ {α β : Type (max u v)} [Finite α] [Finite β]
        (A : Structure L α) (B₀ : Structure L β),
        K.toAmalgamationClass.mem A → E B₀ →
          TreeLike.HasLocallyFiniteAutomorphismPreservingCompletion
            act A B₀ K.toAmalgamationClass) :
    K.toAmalgamationClass.HasCoherentEPPA := by
  exact K.locallyFiniteSubclass_hasCoherentEPPA
    act E hSub hE hIrr hLocallyFinite

/-- **Proposition 11.3:** ordinary Γ-homomorphism-embedding
completion into a hereditary finite strong-amalgamation class
exists if and only if a globally injective such completion
exists. This does *not* assert an automorphism-preserving lift. -/
theorem completionIffStrong
    (act : L.Action Γ)
    (K : TreeLike.HereditaryFiniteStrongAmalgamationClass act)
    {V : Type v} [Finite V] (A : Structure L V) :
    K.toAmalgamationClass.HasCompletion A ↔
      K.toAmalgamationClass.HasStrongCompletion A := by
  exact TreeLike.strongCompletion_proposition_11_3 act K A

end MainTheorems
end AllThoseEPPA
