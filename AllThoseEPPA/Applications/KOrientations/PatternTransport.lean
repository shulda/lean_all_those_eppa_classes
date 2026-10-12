import AllThoseEPPA.Applications.KOrientations.AuxiliaryLanguage
import Mathlib.GroupTheory.Perm.Basic

/-!
# Equivariant transport of root-pattern labels

A template automorphism acts on P=(x, root-enumeration) by applying
the same permutation to the template vertex and every coordinate of
the root enumeration. This lemma packages the exact hypotheses:
root status and complete root-set membership must be preserved.

It is the algebraic ingredient of the later nonfaithful Gamma-action
on the auxiliary relation symbols R_P and E_P.
-/

namespace AllThoseEPPA.Applications.KOrientations

universe u

namespace RootPattern

variable {V : Type u} [Fintype V]
variable (G : Digraph V) (k : ℕ)

/-- Transport an indexed non-root label along a vertex permutation
that preserves root status and full reachable-root sets. -/
def transport (g : Equiv.Perm V)
    (hRoot : ∀ v : V, G.IsRoot k (g v) ↔ G.IsRoot k v)
    (hRoots : ∀ v : V,
      G.roots k (g v) = g '' G.roots k v)
    {n : ℕ} (P : RootPattern G k n) :
    RootPattern G k n where
  center := g P.center
  nonroot := by
    intro hx
    exact P.nonroot ((hRoot P.center).1 hx)
  positive := P.positive
  tuple := g ∘ P.tuple
  injective := g.injective.comp P.injective
  roots_eq := by
    calc
      G.roots k (g P.center) = g '' G.roots k P.center :=
        hRoots P.center
      _ = g '' Set.range P.tuple :=
        congrArg (fun S : Set V => g '' S) P.roots_eq
      _ = Set.range (g ∘ P.tuple) := by
        rw [Set.range_comp]

@[simp] theorem transport_center
    (g : Equiv.Perm V)
    (hRoot : ∀ v, G.IsRoot k (g v) ↔ G.IsRoot k v)
    (hRoots : ∀ v, G.roots k (g v) = g '' G.roots k v)
    {n : ℕ} (P : RootPattern G k n) :
    (transport G k g hRoot hRoots P).center = g P.center :=
  rfl

@[simp] theorem transport_tuple
    (g : Equiv.Perm V)
    (hRoot : ∀ v, G.IsRoot k (g v) ↔ G.IsRoot k v)
    (hRoots : ∀ v, G.roots k (g v) = g '' G.roots k v)
    {n : ℕ} (P : RootPattern G k n) (i : Fin n) :
    (transport G k g hRoot hRoots P).tuple i = g (P.tuple i) :=
  rfl

end RootPattern

end AllThoseEPPA.Applications.KOrientations
