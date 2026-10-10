import AllThoseEPPA.TreeLikeIrreducibleEmbeddingImage
import AllThoseEPPA.AutomorphismPreservingEPPATransfer

/-!
# Exact irreducible copies survive strong completions

A homomorphism-embedding B → C need not be an exact embedding
globally. However, if A is irreducible and e : A ↪ B is exact,
the image e(A) is a closed irreducible induced substructure of B.
The homomorphism-embedding B → C is *exact there*, hence its
composition with e is an exact Γ-embedding A ↪ C.

This closes the extra assumption in the earlier formalization of
EPPA/coherent EPPA transport through automorphism-preserving
strong completions. It also supplies the precise bridge required
in the proof of manuscript Theorem 1.6, where A is irreducible.
-/

namespace AllThoseEPPA
namespace Structure
namespace Homomorphism

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x} {X : Type y}

/-- Composition of an exact embedding of irreducible A with an
arbitrary Γ-homomorphism-embedding is again an *exact* Γ-embedding.
No global injectivity of the second map, finite carrier, or
unary-function assumption is required. -/
def compEmbedding_of_irreducible
    (act : L.Action Γ)
    {A : Structure L V} {B : Structure L W}
    {C : Structure L X}
    (g : Homomorphism act B C)
    (hg : IsHomomorphismEmbedding act g)
    (e : Embedding act A B)
    (hA : A.IsIrreducible) :
    Embedding act A C := by
  let S : Set W := Set.range e.toFun
  have hS : B.IsClosed S := e.range_isClosed act
  have hIrrS : (B.induce S hS).IsIrreducible :=
    e.range_isIrreducible act hA
  have hLocal : IsEmbeddingOn act g S := hg S hS hIrrS
  refine
    { lang := g.lang * e.lang
      toFun := g.toFun ∘ e.toFun
      injective := ?_
      map_rel_iff := ?_
      map_func := ?_ }
  · intro a b hab
    apply e.injective
    exact hLocal.1 ⟨a, rfl⟩ ⟨b, rfl⟩ hab
  · intro n R xs
    have hTuple : ∀ i, (e.toFun ∘ xs) i ∈ S := by
      intro i
      exact ⟨xs i, rfl⟩
    have hG := hLocal.2.1
      (act.onRel e.lang R) (e.toFun ∘ xs) hTuple
    have hE := e.map_rel_iff R xs
    simpa only [Language.Action.onRel_mul, Function.comp_assoc]
      using hG.trans hE
  · intro n F xs
    have hTuple : ∀ i, (e.toFun ∘ xs) i ∈ S := by
      intro i
      exact ⟨xs i, rfl⟩
    have hG := hLocal.2.2
      (act.onFunc e.lang F) (e.toFun ∘ xs) hTuple
    have hE := e.map_func F xs
    change imageSet (g.toFun ∘ e.toFun) (A.func F xs) =
      C.func (act.onFunc (g.lang * e.lang) F)
        ((g.toFun ∘ e.toFun) ∘ xs)
    calc
      imageSet (g.toFun ∘ e.toFun) (A.func F xs) =
          imageSet g.toFun (imageSet e.toFun (A.func F xs)) :=
            (imageSet_comp g.toFun e.toFun (A.func F xs)).symm
      _ = imageSet g.toFun
            (B.func (act.onFunc e.lang F) (e.toFun ∘ xs)) := by
          rw [hE]
      _ = C.func (act.onFunc g.lang (act.onFunc e.lang F))
            (g.toFun ∘ (e.toFun ∘ xs)) :=
          hG
      _ = C.func (act.onFunc (g.lang * e.lang) F)
            ((g.toFun ∘ e.toFun) ∘ xs) := by
          rw [← Language.Action.onFunc_mul]
          rfl

end Homomorphism

namespace AutomorphismPreservingStrongCompletion

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x} {X : Type y}
variable {act : L.Action Γ}
variable {A : Structure L V} {B : Structure L W} {C : Structure L X}

/-- The canonical embedded A-copy in the completed witness,
with **no independent embedding assumption**: irreducibility
of A and the exact embedding into B suffice. -/
def completedEmbedding
    (c : AutomorphismPreservingStrongCompletion act B C)
    (ψ : Embedding act A B)
    (hA : A.IsIrreducible) :
    Embedding act A C :=
  Homomorphism.compEmbedding_of_irreducible
    act c.toHomomorphism c.homomorphismEmbedding ψ hA

/-- Plain EPPA survives an automorphism-preserving strong
completion as soon as the distinguished A is irreducible. -/
theorem preservesEPPA_of_irreducible
    (c : AutomorphismPreservingStrongCompletion act B C)
    (ψ : Embedding act A B)
    (hA : A.IsIrreducible)
    (hEPPA : IsEPPAWitness act ψ) :
    IsEPPAWitness act (c.completedEmbedding ψ hA) := by
  exact c.preservesEPPA ψ (c.completedEmbedding ψ hA)
    (by intro a; rfl) rfl hEPPA

/-- The analogue for coherent EPPA, including the exact
language component of every automorphism extension. -/
theorem preservesCoherentEPPA_of_irreducible
    (c : AutomorphismPreservingStrongCompletion act B C)
    (ψ : Embedding act A B)
    (hA : A.IsIrreducible)
    (hCoh : IsCoherentEPPAWitness act ψ) :
    IsCoherentEPPAWitness act (c.completedEmbedding ψ hA) := by
  exact c.preservesCoherentEPPA ψ (c.completedEmbedding ψ hA)
    (by intro a; rfl) rfl hCoh

end AutomorphismPreservingStrongCompletion
end Structure
end AllThoseEPPA
