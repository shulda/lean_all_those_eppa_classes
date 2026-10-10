import AllThoseEPPA.Automorphism
import AllThoseEPPA.TreeLikeHomEmbComposition

/-!
# Automorphism-preserving strong completions

The further completion/local-finiteness consequences of the
Herwig--Lascar theorem use *automorphism-preserving* completions.

A strong completion has an **irreducible target** and need not be an
induced embedding on the entire source: its map is an injective
homomorphism-embedding, so only irreducible closed substructures
must be embedded exactly.
Automorphism preservation additionally supplies a homomorphic lift
of *every* source automorphism to an automorphism of the target.

The homomorphism law is encoded through identity and composition
of the existing total Γ-automorphism API (before introducing an
additional Group instance for it). We explicitly record both the
vertex and the Γ-language components of the commutative square.

Identity and composition of automorphism-preserving completions
are verified here. This is generic in the arities of functions and
relations; the subsequent locally finite class theorem can specialize
to unary-function languages when invoking thm:maintree.
-/

namespace AllThoseEPPA
namespace Structure

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {V : Type w} {W : Type x} {X : Type y}

/-- A strong completion of A in B carrying a composition-compatible
lift of *all* Γ-automorphisms of A. In contrast to an embedding,
the underlying map is allowed to add relations outside the
irreducible pieces. -/
structure AutomorphismPreservingStrongCompletion
    (act : L.Action Γ)
    (A : Structure L V) (B : Structure L W) where
  irreducible_target : B.IsIrreducible
  toHomomorphism : Homomorphism act A B
  injective : Function.Injective toHomomorphism.toFun
  homomorphismEmbedding :
    Homomorphism.IsHomomorphismEmbedding act toHomomorphism
  lift : Automorphism act A → Automorphism act B
  lift_lang :
    ∀ g : Automorphism act A,
      (lift g).lang * toHomomorphism.lang =
        toHomomorphism.lang * g.lang
  lift_apply :
    ∀ (g : Automorphism act A) (a : V),
      lift g (toHomomorphism a) = toHomomorphism (g a)
  lift_id :
    lift (Automorphism.id A) = Automorphism.id B
  lift_comp :
    ∀ g h : Automorphism act A,
      lift (g.comp h) = (lift g).comp (lift h)

namespace AutomorphismPreservingStrongCompletion

variable {act : L.Action Γ}
variable {A : Structure L V} {B : Structure L W} {C : Structure L X}

/-- Every irreducible Γ-structure is an automorphism-preserving
strong completion of itself. -/
noncomputable def identity (act : L.Action Γ) (A : Structure L V)
    (hA : A.IsIrreducible) :
    AutomorphismPreservingStrongCompletion act A A := by
  let e : Embedding act A A := Embedding.id A
  refine {
    irreducible_target := hA
    toHomomorphism := e.toHomomorphism
    injective := e.injective
    homomorphismEmbedding := ?_
    lift := fun g => g
    lift_lang := ?_
    lift_apply := ?_
    lift_id := ?_
    lift_comp := ?_ }
  · intro S hS hIrr
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb hab
      exact e.injective hab
    · intro n R xs hxs
      exact e.map_rel_iff R xs
    · intro n F xs hxs
      exact e.map_func F xs
  · intro g
    change g.lang * 1 = 1 * g.lang
    simp
  · intro g a
    rfl
  · rfl
  · intro g h
    rfl

/-- Composition of automorphism-preserving strong completions.
Both the injectivity and the homomorphism-embedding property
survive, and the automorphism lift is the composite lift. -/
def comp
    (g : AutomorphismPreservingStrongCompletion act B C)
    (f : AutomorphismPreservingStrongCompletion act A B) :
    AutomorphismPreservingStrongCompletion act A C := by
  refine {
    irreducible_target := g.irreducible_target
    toHomomorphism := g.toHomomorphism.comp f.toHomomorphism
    injective := g.injective.comp f.injective
    homomorphismEmbedding :=
      Homomorphism.comp_isHomomorphismEmbedding
        act g.toHomomorphism f.toHomomorphism
        g.homomorphismEmbedding f.homomorphismEmbedding
    lift := fun σ => g.lift (f.lift σ)
    lift_lang := ?_
    lift_apply := ?_
    lift_id := ?_
    lift_comp := ?_ }
  · intro σ
    change (g.lift (f.lift σ)).lang *
        (g.toHomomorphism.lang * f.toHomomorphism.lang) =
      (g.toHomomorphism.lang * f.toHomomorphism.lang) * σ.lang
    calc
      (g.lift (f.lift σ)).lang *
          (g.toHomomorphism.lang * f.toHomomorphism.lang) =
        ((g.lift (f.lift σ)).lang * g.toHomomorphism.lang) *
          f.toHomomorphism.lang := by rw [mul_assoc]
      _ = (g.toHomomorphism.lang * (f.lift σ).lang) *
          f.toHomomorphism.lang := by rw [g.lift_lang (f.lift σ)]
      _ = g.toHomomorphism.lang *
          ((f.lift σ).lang * f.toHomomorphism.lang) := by
            rw [mul_assoc]
      _ = g.toHomomorphism.lang *
          (f.toHomomorphism.lang * σ.lang) := by
            rw [f.lift_lang σ]
      _ = (g.toHomomorphism.lang * f.toHomomorphism.lang) *
          σ.lang := by rw [mul_assoc]
  · intro σ a
    change (g.lift (f.lift σ))
      (g.toHomomorphism (f.toHomomorphism a)) =
      g.toHomomorphism (f.toHomomorphism (σ a))
    rw [g.lift_apply (f.lift σ) (f.toHomomorphism a),
        f.lift_apply σ a]
  · change g.lift (f.lift (Automorphism.id A)) =
      Automorphism.id C
    rw [f.lift_id, g.lift_id]
  · intro σ τ
    change g.lift (f.lift (σ.comp τ)) =
      (g.lift (f.lift σ)).comp (g.lift (f.lift τ))
    rw [f.lift_comp, g.lift_comp]

end AutomorphismPreservingStrongCompletion
end Structure
end AllThoseEPPA
