import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Set.Finite.Basic
import AllThoseEPPA.Relabelling

/-!
# Compressing an infinite relational language around a finite structure

This file starts the formalization of Proposition `prop:infinite_languages`.
For a finite structure with finite relabelling orbit, all relation information
relevant to partial automorphisms can be encoded by finitely many profiles of
injective tuples.

We keep the original group `Γ` rather than quotienting it by its action on
the finite profile language.  This is equivalent for the construction and
keeps the language component of partial automorphisms literally unchanged.
-/

namespace AllThoseEPPA
namespace InfiniteRelational

universe u v w

variable {L : Language.{u}} [L.IsRelational]
variable {Γ : Type w} [Group Γ]
variable {α : Type v} [Fintype α]
variable (act : L.Action Γ) (A : Structure L α)

/-- A relation symbol together with a surjective coordinate map onto an
`n`-element injective support. -/
structure ProfileEntry (L : Language.{u}) (n : ℕ) where
  arity : ℕ
  symbol : L.RelSymbol arity
  coord : Fin arity → Fin n
  coord_surjective : Function.Surjective coord

/-- The complete relational profile of an injective `n`-tuple. -/
abbrev Profile (L : Language.{u}) (n : ℕ) :=
  Set (ProfileEntry L n)

/-- Profile of a tuple in a structure.  The tuple need not be injective for
the definition, though pattern symbols below only store injective tuples. -/
def profile {β : Type*} (B : Structure L β) {n : ℕ}
    (xs : Fin n → β) : Profile L n :=
  {e | B.rel e.symbol (xs ∘ e.coord)}

/-- Structures in the relabelling orbit of `A`. -/
abbrev Orbit :=
  {B : Structure L α // B ∈ Set.range fun g : Γ => A.relabel act g}

noncomputable def orbitFintype
    (hA : A.HasFiniteRelabelOrbit act) :
    Fintype (Orbit act A) :=
  Set.Finite.fintype hA

/-- An injective finite tuple. -/
abbrev InjTuple (α : Type v) (n : ℕ) :=
  {xs : Fin n → α // Function.Injective xs}

noncomputable def injTupleFintype (n : ℕ) :
    Fintype (InjTuple α n) := by
  classical
  exact Fintype.ofFinite _

/-- A symbol of the compressed finite language: a positive-arity injective
tuple in one member of the finite relabelling orbit.  Different codes with the
same profile are harmless; they simply name duplicate relations. -/
abbrev PatternSymbol (n : ℕ) :=
  {p : Orbit act A × InjTuple α n // 0 < n}

/-- The profile named by a pattern symbol. -/
def patternProfile {n : ℕ} (P : PatternSymbol act A n) :
    Profile L n :=
  profile P.1.1.1 P.1.2.1

/-- Relabel one orbit element. -/
def orbitRelabel (g : Γ) : Orbit act A ≃ Orbit act A where
  toFun := fun B => by
    refine ⟨B.1.relabel act g, ?_⟩
    rcases B.2 with ⟨h, hB⟩
    refine ⟨g * h, ?_⟩
    calc
      A.relabel act (g * h) = (A.relabel act h).relabel act g :=
        (Structure.relabel_mul act g h A).symm
      _ = B.1.relabel act g := congrArg (fun C => C.relabel act g) hB
  invFun := fun B => by
    refine ⟨B.1.relabel act g⁻¹, ?_⟩
    rcases B.2 with ⟨h, hB⟩
    refine ⟨g⁻¹ * h, ?_⟩
    calc
      A.relabel act (g⁻¹ * h) = (A.relabel act h).relabel act g⁻¹ :=
        (Structure.relabel_mul act g⁻¹ h A).symm
      _ = B.1.relabel act g⁻¹ :=
        congrArg (fun C => C.relabel act g⁻¹) hB
  left_inv := by
    intro B
    apply Subtype.ext
    change (B.1.relabel act g).relabel act g⁻¹ = B.1
    rw [Structure.relabel_mul]
    simp
  right_inv := by
    intro B
    apply Subtype.ext
    change (B.1.relabel act g⁻¹).relabel act g = B.1
    rw [Structure.relabel_mul]
    simp

@[simp] theorem orbitRelabel_val (g : Γ) (B : Orbit act A) :
    (orbitRelabel act A g B).1 = B.1.relabel act g :=
  rfl

/-- The original group acts on the finite relabelling orbit. -/
def orbitAction : Γ →* Equiv.Perm (Orbit act A) where
  toFun := orbitRelabel act A
  map_one' := by
    ext B
    change B.1.relabel act 1 = B.1
    simp
  map_mul' := by
    intro g h
    ext B
    change B.1.relabel act (g * h) =
      (B.1.relabel act h).relabel act g
    exact (Structure.relabel_mul act g h B.1).symm

/-- Action on a pattern symbol: relabel the stored orbit structure and keep
the injective coordinate tuple fixed. -/
def patternPerm (g : Γ) {n : ℕ} :
    Equiv.Perm (PatternSymbol act A n) where
  toFun := fun P =>
    ⟨⟨orbitRelabel act A g P.1.1, P.1.2⟩, P.2⟩
  invFun := fun P =>
    ⟨⟨orbitRelabel act A g⁻¹ P.1.1, P.1.2⟩, P.2⟩
  left_inv := by
    intro P
    apply Subtype.ext
    apply Prod.ext
    · exact (orbitRelabel act A g).left_inv P.1.1
    · rfl
  right_inv := by
    intro P
    apply Subtype.ext
    apply Prod.ext
    · exact (orbitRelabel act A g).right_inv P.1.1
    · rfl

/-- The finite profile language attached to `A`. -/
def patternLanguage : Language.{max u v} where
  RelSymbol := fun n => PatternSymbol act A n
  FuncSymbol := fun _ => PEmpty.{max u v + 1}
  relArity_pos := fun P => P.2

instance patternLanguage_isRelational :
    (patternLanguage act A).IsRelational where
  func_isEmpty := fun _ => ⟨PEmpty.elim⟩

/-- The original group acts on the finite pattern language. -/
def patternAction :
    (patternLanguage act A).Action Γ where
  rel n :=
    { toFun := fun g => patternPerm act A g
      map_one' := by
        apply Equiv.ext
        intro P
        apply Subtype.ext
        apply Prod.ext
        · have h := congrArg
            (fun e : Equiv.Perm (Orbit act A) => e P.1.1)
            (orbitAction act A).map_one
          change orbitRelabel act A 1 P.1.1 = P.1.1 at h
          exact h
        · rfl
      map_mul' := by
        intro g h
        apply Equiv.ext
        intro P
        apply Subtype.ext
        apply Prod.ext
        · have hmul := congrArg
            (fun e : Equiv.Perm (Orbit act A) => e P.1.1)
            ((orbitAction act A).map_mul g h)
          change orbitRelabel act A (g * h) P.1.1 =
            orbitRelabel act A g (orbitRelabel act A h P.1.1) at hmul
          exact hmul
        · rfl }
  func _ := 1

noncomputable def patternSymbolFintype
    (hA : A.HasFiniteRelabelOrbit act) (n : ℕ) :
    Fintype ((patternLanguage act A).RelSymbol n) := by
  letI : Fintype (Orbit act A) := orbitFintype act A hA
  letI : Fintype (InjTuple α n) := injTupleFintype n
  classical
  haveI : Finite ((patternLanguage act A).RelSymbol n) :=
    Finite.of_injective
      (fun P : PatternSymbol act A n => P.1)
      Subtype.val_injective
  exact Fintype.ofFinite _

/-- Every pattern arity is bounded by the size of the original finite vertex
set. -/
theorem patternSymbol_arity_le
    {n : ℕ} (P : (patternLanguage act A).RelSymbol n) :
    n ≤ Fintype.card α := by
  simpa using
    Fintype.card_le_of_injective P.1.2.1 P.1.2.2

/-- A finite code type containing all relation symbols of the pattern
language. -/
abbrev BoundedPatternCode :=
  Σ k : Fin (Fintype.card α + 1),
    (patternLanguage act A).RelSymbol k.1

noncomputable def boundedPatternCodeFintype
    (hA : A.HasFiniteRelabelOrbit act) :
    Fintype (BoundedPatternCode act A) := by
  letI : Fintype (Orbit act A) := orbitFintype act A hA
  letI (n : ℕ) : Fintype (InjTuple α n) := injTupleFintype n
  letI (n : ℕ) : Fintype ((patternLanguage act A).RelSymbol n) :=
    patternSymbolFintype act A hA n
  infer_instance

/-- Embed every bundled pattern symbol into the bounded finite code type. -/
noncomputable def anyPatternToBounded
    (P : (patternLanguage act A).AnyRelSymbol) :
    BoundedPatternCode act A := by
  classical
  rcases P with ⟨n, P⟩
  have hn : n < Fintype.card α + 1 :=
    Nat.lt_succ_iff.mpr (patternSymbol_arity_le act A P)
  exact ⟨⟨n, hn⟩, P⟩

/-- Forget the arity bound from a bounded pattern code. -/
def boundedToAnyPattern
    (P : BoundedPatternCode act A) :
    (patternLanguage act A).AnyRelSymbol :=
  ⟨P.1.1, P.2⟩

theorem boundedToAnyPattern_anyPatternToBounded
    (P : (patternLanguage act A).AnyRelSymbol) :
    boundedToAnyPattern act A (anyPatternToBounded act A P) = P := by
  rcases P with ⟨n, P⟩
  rfl

theorem anyPatternToBounded_injective :
    Function.Injective (anyPatternToBounded act A) := by
  intro P Q h
  rcases P with ⟨n, P⟩
  rcases Q with ⟨m, Q⟩
  have hk := (Sigma.mk.inj_iff.mp h).1
  have hnm : n = m := congrArg Fin.val hk
  subst m
  have hheq := (Sigma.mk.inj_iff.mp h).2
  have hPQ : P = Q := eq_of_heq hheq
  subst Q
  rfl

/-- The compressed pattern language has finitely many relation symbols in
total, even though the original language may be infinite. -/
theorem patternAnyRelFinite
    (hA : A.HasFiniteRelabelOrbit act) :
    Finite (patternLanguage act A).AnyRelSymbol := by
  letI : Fintype (BoundedPatternCode act A) :=
    boundedPatternCodeFintype act A hA
  exact Finite.of_injective
    (anyPatternToBounded act A)
    (anyPatternToBounded_injective act A)

end InfiniteRelational
end AllThoseEPPA
