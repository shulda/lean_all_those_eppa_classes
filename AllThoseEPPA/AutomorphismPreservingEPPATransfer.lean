import AllThoseEPPA.AutomorphismPreservingCompletion

/-!
# EPPA transport through automorphism-preserving strong completions

In the proof of the locally finite class theorem, a finite locally
tree-like EPPA witness B is automorphism-preservingly completed to C.
The original A-copy must remain an *embedding* in C: a strong
completion is an injective homomorphism-embedding, which is not
necessarily a global exact embedding.

We separate this genuine structural obligation from the easy
automorphism transport. Once an embedding ι : A → C is available
with the same Γ-language and vertex components as the composite,
all extension equations transport, and a *coherent* extension
system remains coherent because the completion's automorphism
lift preserves composition and equality.

These lemmas do not assume that C itself is an EPPA witness
before the completion, nor do they assume global exactness of
B → C.
-/

namespace AllThoseEPPA
namespace Structure
namespace AutomorphismPreservingStrongCompletion

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {act : L.Action Γ}
variable {V : Type w} {W : Type x} {X : Type y}
variable {A : Structure L V} {B : Structure L W} {C : Structure L X}

/-- A lifted automorphism extends a partial automorphism of the
original structure along an exact A-copy in the completion.
The equality of *language* components is part of the proof. -/
theorem extendsAlong_post
    (c : AutomorphismPreservingStrongCompletion act B C)
    (ψ : Embedding act A B)
    (ι : Embedding act A C)
    (hVertex : ∀ a : V,
      ι a = c.toHomomorphism (ψ a))
    (hLang :
      ι.lang = c.toHomomorphism.lang * ψ.lang)
    (p : PartialAutomorphism act A)
    (σ : Automorphism act B)
    (hExt : ExtendsAlong act ψ p σ) :
    ExtendsAlong act ι p (c.lift σ) := by
  constructor
  · calc
      (c.lift σ).lang * ι.lang =
          (c.lift σ).lang *
            (c.toHomomorphism.lang * ψ.lang) := by rw [hLang]
      _ = ((c.lift σ).lang * c.toHomomorphism.lang) * ψ.lang := by
          rw [mul_assoc]
      _ = (c.toHomomorphism.lang * σ.lang) * ψ.lang := by
          rw [c.lift_lang σ]
      _ = c.toHomomorphism.lang * (σ.lang * ψ.lang) := by
          rw [mul_assoc]
      _ = c.toHomomorphism.lang * (ψ.lang * p.lang) := by
          rw [hExt.1]
      _ = (c.toHomomorphism.lang * ψ.lang) * p.lang := by
          rw [mul_assoc]
      _ = ι.lang * p.lang := by rw [hLang]
  · intro a ha
    calc
      c.lift σ (ι a) =
          c.lift σ (c.toHomomorphism (ψ a)) := by
            rw [hVertex a]
      _ = c.toHomomorphism (σ (ψ a)) :=
        c.lift_apply σ (ψ a)
      _ = c.toHomomorphism (ψ (p a)) := by
        rw [hExt.2 a ha]
      _ = ι (p a) := (hVertex (p a)).symm

/-- EPPA extends along an automorphism-preserving completion,
provided the designated copy of A is still an exact embedding. -/
theorem preservesEPPA
    (c : AutomorphismPreservingStrongCompletion act B C)
    (ψ : Embedding act A B)
    (ι : Embedding act A C)
    (hVertex : ∀ a : V,
      ι a = c.toHomomorphism (ψ a))
    (hLang :
      ι.lang = c.toHomomorphism.lang * ψ.lang)
    (hEPPA : IsEPPAWitness act ψ) :
    IsEPPAWitness act ι := by
  intro p
  obtain ⟨σ, hExt⟩ := hEPPA p
  exact ⟨c.lift σ,
    c.extendsAlong_post ψ ι hVertex hLang p σ hExt⟩

/-- The actual coherent selector on a completed witness is the
composite of the old coherent selector with the completion's
automorphism lift. -/
def coherentExtension_post
    (c : AutomorphismPreservingStrongCompletion act B C)
    (ψ : Embedding act A B)
    (ι : Embedding act A C)
    (hVertex : ∀ a : V,
      ι a = c.toHomomorphism (ψ a))
    (hLang :
      ι.lang = c.toHomomorphism.lang * ψ.lang)
    (e : CoherentExtension act ψ) :
    CoherentExtension act ι where
  extension := fun p => c.lift (e.extension p)
  extension_spec := by
    intro p
    exact c.extendsAlong_post ψ ι hVertex hLang p
      (e.extension p) (e.extension_spec p)
  respects_equivalent := by
    intro p q hpq
    exact congrArg c.lift (e.respects_equivalent p q hpq)
  coherent := by
    intro p q r htriple
    change c.lift (e.extension r) =
      (c.lift (e.extension q)).comp (c.lift (e.extension p))
    rw [e.coherent p q r htriple, c.lift_comp]

/-- Coherent EPPA is retained by an automorphism-preserving strong
completion whenever the distinguished A-copy stays embedded. -/
theorem preservesCoherentEPPA
    (c : AutomorphismPreservingStrongCompletion act B C)
    (ψ : Embedding act A B)
    (ι : Embedding act A C)
    (hVertex : ∀ a : V,
      ι a = c.toHomomorphism (ψ a))
    (hLang :
      ι.lang = c.toHomomorphism.lang * ψ.lang)
    (hCoh : IsCoherentEPPAWitness act ψ) :
    IsCoherentEPPAWitness act ι := by
  obtain ⟨e⟩ := hCoh
  exact ⟨c.coherentExtension_post ψ ι hVertex hLang e⟩

end AutomorphismPreservingStrongCompletion
end Structure
end AllThoseEPPA
