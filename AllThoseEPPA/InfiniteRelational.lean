import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Set.Finite.Basic
import AllThoseEPPA.Relabelling
import AllThoseEPPA.EPPA
import AllThoseEPPA.RelationalExtension

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

universe u v w z t

variable {L : Language.{u}} [L.IsRelational]
variable {Γ : Type w} [Group Γ]
variable {α : Type v} [Fintype α]
variable (act : L.Action Γ) (A : Structure L α)

/-- A relation symbol together with a surjective coordinate map onto an
`n`-element injective support. -/
@[ext] structure ProfileEntry (L : Language.{u}) (n : ℕ) where
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


/-- Relabel the relation-symbol coordinate of one profile entry. -/
def relabelProfileEntry (g : Γ) {n : ℕ}
    (e : ProfileEntry L n) : ProfileEntry L n where
  arity := e.arity
  symbol := act.onRel g e.symbol
  coord := e.coord
  coord_surjective := e.coord_surjective

@[simp] theorem relabelProfileEntry_inv_apply
    (g : Γ) {n : ℕ} (e : ProfileEntry L n) :
    relabelProfileEntry act g⁻¹ (relabelProfileEntry act g e) = e := by
  cases e
  simp [relabelProfileEntry, ← Language.Action.onRel_mul]

@[simp] theorem relabelProfileEntry_apply_inv
    (g : Γ) {n : ℕ} (e : ProfileEntry L n) :
    relabelProfileEntry act g (relabelProfileEntry act g⁻¹ e) = e := by
  cases e
  simp [relabelProfileEntry, ← Language.Action.onRel_mul]

/-- Relabel a profile by the original language action.  The inverse in the
membership test matches the convention used by `Structure.relabel`. -/
def relabelProfile (g : Γ) {n : ℕ}
    (X : Profile L n) : Profile L n :=
  {e | relabelProfileEntry act g⁻¹ e ∈ X}

@[simp] theorem relabelProfile_inv_apply
    (g : Γ) {n : ℕ} (X : Profile L n) :
    relabelProfile act g⁻¹ (relabelProfile act g X) = X := by
  ext e
  simp [relabelProfile]

theorem relabelProfile_injective
    (g : Γ) {n : ℕ} :
    Function.Injective (relabelProfile act g : Profile L n → Profile L n) :=
  Function.LeftInverse.injective (relabelProfile_inv_apply act g)

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

/-- The profile named by a pattern symbol transforms equivariantly under the
pattern-language action. -/
@[simp] theorem patternProfile_patternPerm_relabelProfile
    (g : Γ) {n : ℕ} (P : PatternSymbol act A n) :
    patternProfile act A (patternPerm act A g P) =
      relabelProfile act g (patternProfile act A P) := by
  ext e
  rfl

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


@[simp] theorem patternAction_onRel
    (g : Γ) {n : ℕ} (P : (patternLanguage act A).RelSymbol n) :
    (patternAction act A).onRel g P = patternPerm act A g P :=
  rfl

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



/-- Relabelling a profile along an embedding is exactly relabelling its
relation-symbol coordinate. -/
theorem profile_embedding
    {β : Type z} {γ : Type t}
    {B : Structure L β} {C : Structure L γ}
    (f : Structure.Embedding act B C)
    {n : ℕ} (xs : Fin n → β) :
    profile C (f.toFun ∘ xs) =
      relabelProfile act f.lang (profile B xs) := by
  ext e
  change
    C.rel e.symbol ((f.toFun ∘ xs) ∘ e.coord) ↔
      B.rel (act.onRel f.lang⁻¹ e.symbol) (xs ∘ e.coord)
  have h :=
    f.map_rel_iff (act.onRel f.lang⁻¹ e.symbol) (xs ∘ e.coord)
  have hs :
      act.onRel f.lang (act.onRel f.lang⁻¹ e.symbol) = e.symbol := by
    rw [← Language.Action.onRel_mul]
    simp
  rw [hs] at h
  simpa [Function.comp_assoc] using h

/-- The profile encoding `T(B)`: an injective tuple satisfies the pattern
symbol `P` exactly when its complete original-language profile is the
profile named by `P`. -/
def encodeStructure {β : Type z} (B : Structure L β) :
    Structure (patternLanguage act A) β where
  rel := by
    intro n P xs
    exact Function.Injective xs ∧
      profile B xs = patternProfile act A P
  func := by
    intro n F xs
    exact PEmpty.elim F

@[simp] theorem encodeStructure_rel
    {β : Type z} (B : Structure L β)
    {n : ℕ} (P : (patternLanguage act A).RelSymbol n)
    (xs : Fin n → β) :
    (encodeStructure act A B).rel P xs ↔
      Function.Injective xs ∧
        profile B xs = patternProfile act A P :=
  Iff.rfl

/-- The profile encoding is functorial on embeddings.  This is the first half
of Lemma `lem:functors` in the paper. -/
def encodeEmbedding
    {β : Type z} {γ : Type t}
    {B : Structure L β} {C : Structure L γ}
    (f : Structure.Embedding act B C) :
    Structure.Embedding (patternAction act A)
      (encodeStructure act A B) (encodeStructure act A C) where
  lang := f.lang
  toFun := f.toFun
  injective := f.injective
  map_rel_iff := by
    intro n P xs
    change
      (Function.Injective (f.toFun ∘ xs) ∧
        profile C (f.toFun ∘ xs) =
          patternProfile act A (patternPerm act A f.lang P)) ↔
      (Function.Injective xs ∧
        profile B xs = patternProfile act A P)
    constructor
    · rintro ⟨hinj, hprofile⟩
      have hxs : Function.Injective xs := by
        intro i j hij
        exact hinj (congrArg f.toFun hij)
      refine ⟨hxs, ?_⟩
      apply relabelProfile_injective act f.lang
      rw [← profile_embedding act f xs]
      rw [← patternProfile_patternPerm_relabelProfile act A f.lang P]
      exact hprofile
    · rintro ⟨hinj, hprofile⟩
      refine ⟨f.injective.comp hinj, ?_⟩
      rw [profile_embedding act f xs]
      rw [patternProfile_patternPerm_relabelProfile act A f.lang P]
      exact congrArg (relabelProfile act f.lang) hprofile
  map_func := by
    intro n F xs
    exact PEmpty.elim F



/-- A partial automorphism transforms tuple profiles exactly by the
corresponding action on profile entries. -/
theorem profile_partialAutomorphism
    (p : Structure.PartialAutomorphism act A)
    {n : ℕ} (xs : Fin n → α)
    (hxs : ∀ i, xs i ∈ p.source) :
    profile A (p.toPartialEquiv ∘ xs) =
      relabelProfile act p.lang (profile A xs) := by
  ext e
  change
    A.rel e.symbol ((p.toPartialEquiv ∘ xs) ∘ e.coord) ↔
      A.rel (act.onRel p.lang⁻¹ e.symbol) (xs ∘ e.coord)
  have hdom :
      ∀ i, (xs ∘ e.coord) i ∈ p.source := by
    intro i
    exact hxs (e.coord i)
  have hp :=
    p.map_rel_iff (act.onRel p.lang⁻¹ e.symbol)
      (xs ∘ e.coord) hdom
  have hs :
      act.onRel p.lang (act.onRel p.lang⁻¹ e.symbol) = e.symbol := by
    rw [← Language.Action.onRel_mul]
    simp
  rw [hs] at hp
  simpa [Function.comp_assoc] using hp

/-- The finite pattern structure `T(A)` from the paper. -/
abbrev patternStructure :=
  encodeStructure act A A

/-- Profile equality in a pattern relation is preserved and reflected by a
partial automorphism of the original structure. -/
theorem patternProfile_map_iff
    (p : Structure.PartialAutomorphism act A)
    {n : ℕ} (P : PatternSymbol act A n)
    (xs : Fin n → α) (hxs : ∀ i, xs i ∈ p.source) :
    profile A (p.toPartialEquiv ∘ xs) =
        patternProfile act A (patternPerm act A p.lang P) ↔
      profile A xs = patternProfile act A P := by
  rw [profile_partialAutomorphism act A p xs hxs]
  rw [patternProfile_patternPerm_relabelProfile act A p.lang P]
  exact (relabelProfile_injective act p.lang).eq_iff

/-- Every partial automorphism of `A` induces, with exactly the same language
component and vertex partial equivalence, a partial automorphism of `T(A)`. -/
def liftPartialAutomorphism
    (p : Structure.PartialAutomorphism act A) :
    Structure.PartialAutomorphism (patternAction act A)
      (patternStructure act A) where
  lang := p.lang
  toPartialEquiv := p.toPartialEquiv
  source_closed := by
    intro n F xs hxs
    exact PEmpty.elim F
  target_closed := by
    intro n F xs hxs
    exact PEmpty.elim F
  map_rel_iff := by
    intro n P xs hxs
    change
      (Function.Injective (p.toPartialEquiv ∘ xs) ∧
        profile A (p.toPartialEquiv ∘ xs) =
          patternProfile act A (patternPerm act A p.lang P)) ↔
      (Function.Injective xs ∧
        profile A xs = patternProfile act A P)
    constructor
    · rintro ⟨hinj, hprof⟩
      refine ⟨?_, (patternProfile_map_iff act A p P xs hxs).1 hprof⟩
      intro i j hij
      apply hinj
      exact congrArg p.toPartialEquiv hij
    · rintro ⟨hinj, hprof⟩
      refine ⟨?_, (patternProfile_map_iff act A p P xs hxs).2 hprof⟩
      intro i j hij
      apply hinj
      exact p.toPartialEquiv.injOn (hxs i) (hxs j) hij
  map_func := by
    intro n F xs hxs
    exact PEmpty.elim F

@[simp] theorem liftPartialAutomorphism_lang
    (p : Structure.PartialAutomorphism act A) :
    (liftPartialAutomorphism act A p).lang = p.lang :=
  rfl

@[simp] theorem liftPartialAutomorphism_partialEquiv
    (p : Structure.PartialAutomorphism act A) :
    (liftPartialAutomorphism act A p).toPartialEquiv = p.toPartialEquiv :=
  rfl

/-- Extensional equality of original partial automorphisms is preserved by the
lift to the pattern structure. -/
theorem liftPartialAutomorphism_equivalent
    {p q : Structure.PartialAutomorphism act A}
    (hpq : Structure.PartialIsomorphism.Equivalent p q) :
    Structure.PartialIsomorphism.Equivalent
      (liftPartialAutomorphism act A p)
      (liftPartialAutomorphism act A q) :=
  hpq


/-- Lifting partial automorphisms to the pattern structure preserves coherent
triples verbatim: the language component and the underlying partial
equivalence are unchanged. -/
theorem liftPartialAutomorphism_coherentTriple
    {p q r : Structure.PartialAutomorphism act A}
    (h : Structure.PartialIsomorphism.CoherentTriple p q r) :
    Structure.PartialIsomorphism.CoherentTriple
      (liftPartialAutomorphism act A p)
      (liftPartialAutomorphism act A q)
      (liftPartialAutomorphism act A r) := by
  rcases h with ⟨htg, hr⟩
  refine ⟨htg, ?_⟩
  exact hr

/-- The finite pattern encoding of A has a finite coherent EPPA-witness by
the already formalized finite-language relational construction. -/
theorem patternStructure_hasCoherentEPPA
    (hA : A.HasFiniteRelabelOrbit act) :
    ∃ ψ : Structure.Embedding (patternAction act A)
        (patternStructure act A)
        (Relational.witnessStructure (L := patternLanguage act A) α),
      Structure.IsCoherentEPPAWitness (patternAction act A) ψ := by
  letI : Finite (patternLanguage act A).AnyRelSymbol :=
    patternAnyRelFinite act A hA
  exact
    Relational.finiteRelationalStructuresHaveCoherentEPPA
      (act := patternAction act A) (patternStructure act A)

end InfiniteRelational
end AllThoseEPPA
