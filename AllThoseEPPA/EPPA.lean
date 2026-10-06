import AllThoseEPPA.PartialIso

/-!
# EPPA and coherent EPPA

The definitions here are arranged around an explicit embedding ψ : A ↪ B.
Rather than first replacing A by its image ψ(A), extension is expressed by the
commuting equation g ∘ ψ = ψ ∘ p on the domain of a partial automorphism p.
For the language components this reads g_L ψ_L = ψ_L p_L.  This is equivalent
to the paper's formulation using partial automorphisms of ψ(A), and avoids
rebuilding an image structure merely to state EPPA.
-/

namespace AllThoseEPPA

universe u v w z

namespace Structure

variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable (act : L.Action Γ)
variable {V : Type w} {W : Type z}

/-- A partial automorphism is a partial isomorphism from a structure to itself. -/
abbrev PartialAutomorphism (A : Structure L V) :=
  PartialIsomorphism act A A

/-- An automorphism is a partial automorphism whose domain and range are the
whole vertex set. -/
structure Automorphism (A : Structure L V) where
  toPartialIsomorphism : PartialAutomorphism act A
  source_eq_univ : toPartialIsomorphism.source = Set.univ
  target_eq_univ : toPartialIsomorphism.target = Set.univ

instance {A : Structure L V} :
    CoeFun (Automorphism act A) (fun _ => V → V) :=
  ⟨fun g => g.toPartialIsomorphism⟩

namespace Automorphism

variable {act : L.Action Γ}
variable {A : Structure L V}

/-- Language component of an automorphism. -/
def lang (g : Automorphism act A) : Γ :=
  g.toPartialIsomorphism.lang

/-- Identity automorphism. -/
def id (A : Structure L V) : Automorphism act A where
  toPartialIsomorphism :=
    PartialIsomorphism.reflOn A Set.univ (isClosed_univ A)
  source_eq_univ := rfl
  target_eq_univ := rfl

/-- Composition of automorphisms. -/
def comp (g f : Automorphism act A) : Automorphism act A := by
  have h :
      f.toPartialIsomorphism.target =
        g.toPartialIsomorphism.source := by
    rw [f.target_eq_univ, g.source_eq_univ]
  refine
    { toPartialIsomorphism :=
        g.toPartialIsomorphism.comp f.toPartialIsomorphism h
      source_eq_univ := ?_
      target_eq_univ := ?_ }
  · change f.toPartialIsomorphism.toPartialEquiv.source = Set.univ
    exact f.source_eq_univ
  · change g.toPartialIsomorphism.toPartialEquiv.target = Set.univ
    exact g.target_eq_univ

@[simp] theorem comp_apply (g f : Automorphism act A) (x : V) :
    g.comp f x = g (f x) :=
  rfl

@[simp] theorem comp_lang (g f : Automorphism act A) :
    (g.comp f).lang = g.lang * f.lang :=
  rfl

end Automorphism

/-- A total automorphism g of B extends a partial automorphism p of A along an
embedding ψ : A ↪ B if the obvious square commutes, including on the language
components. -/
def ExtendsAlong {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B) (p : PartialAutomorphism act A)
    (g : Automorphism act B) : Prop :=
  g.lang * ψ.lang = ψ.lang * p.lang ∧
    ∀ x, x ∈ p.source → g (ψ x) = ψ (p x)

/-- B is an EPPA-witness for A with respect to the chosen embedding ψ. -/
def IsEPPAWitness {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B) : Prop :=
  ∀ p : PartialAutomorphism act A,
    ∃ g : Automorphism act B, ExtendsAlong ψ p g

/-- A coherent simultaneous choice of extensions of all partial automorphisms. -/
structure CoherentExtension {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B) where
  extension : PartialAutomorphism act A → Automorphism act B
  extends : ∀ p, ExtendsAlong ψ p (extension p)
  coherent :
    ∀ f g h : PartialAutomorphism act A,
      PartialIsomorphism.CoherentTriple f g h →
        extension h = (extension g).comp (extension f)

/-- B is a coherent EPPA-witness for A with respect to ψ. -/
def IsCoherentEPPAWitness {A : Structure L V} {B : Structure L W}
    (ψ : Embedding act A B) : Prop :=
  Nonempty (CoherentExtension act ψ)

theorem CoherentExtension.isEPPAWitness
    {A : Structure L V} {B : Structure L W}
    {ψ : Embedding act A B} (e : CoherentExtension act ψ) :
    IsEPPAWitness act ψ := by
  intro p
  exact ⟨e.extension p, e.extends p⟩

end Structure
end AllThoseEPPA
