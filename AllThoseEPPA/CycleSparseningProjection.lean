import AllThoseEPPA.CycleSparseningWitness

/-!
# Projection from the cycle-sparsening witness

This file formalizes the projection part of Claim `c:cycles:b`: projection
to the first coordinate is a homomorphism, preserves unary function fibres
exactly, and is an embedding on every generic set of witness vertices.
-/

namespace AllThoseEPPA
namespace Sparsening

universe u v w

variable {L : Language.{u}} [L.HasUnaryFunctions]
variable {Γ : Type v} [Group Γ]
variable {V : Type w}
variable (act : L.Action Γ)
variable (B₀ : Structure L V)
variable (E : L.RelSymbol 2)

/-- Projection of the cycle-sparsening witness to the base witness. -/
noncomputable def projection :
    Structure.Homomorphism act
      (witnessStructure B₀ E) B₀ where
  lang := 1
  toFun := fun w => WitnessVertex.base B₀ E w
  map_rel := by
    intro n R xs hrel
    simpa [Function.comp_def] using hrel.1
  map_func := by
    intro n F xs
    have hxs :
        xs = fun _ => xs (UnaryFunctions.unaryIndex F) :=
      UnaryFunctions.unaryTuple_eq_constant F xs
    rw [hxs]
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    change
      z ∈
        (witnessStructure B₀ E).func F
          (fun _ => xs (UnaryFunctions.unaryIndex F)) at hz
    rcases hz with ⟨b, hb, rfl⟩
    simpa [Function.comp_def, functionValueVertex,
      WitnessVertex.base] using hb

@[simp] theorem projection_apply
    (w : WitnessVertex B₀ E) :
    projection act B₀ E w = WitnessVertex.base B₀ E w :=
  rfl

/-- Projection maps each unary witness-function fibre exactly onto the
corresponding base-witness function fibre. -/
theorem projection_map_func_eq_constant
    {n : ℕ} (F : L.FuncSymbol n)
    (w : WitnessVertex B₀ E) :
    Structure.imageSet
        (projection act B₀ E).toFun
        ((witnessStructure B₀ E).func F (fun _ => w)) =
      B₀.func F
        (fun _ => WitnessVertex.base B₀ E w) := by
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    rcases hz with ⟨b, hb, hzb⟩
    subst z
    have hby : b = y := by
      simpa [projection, functionValueVertex,
        WitnessVertex.base] using hzy
    subst y
    exact hb
  · intro hy
    refine
      ⟨functionValueVertex B₀ E w F y hy, ?_, ?_⟩
    · exact ⟨y, hy, rfl⟩
    · rfl

/-- Projection preserves unary function fibres by equality. -/
theorem projection_map_func_eq
    {n : ℕ} (F : L.FuncSymbol n)
    (xs : Fin n → WitnessVertex B₀ E) :
    Structure.imageSet
        (projection act B₀ E).toFun
        ((witnessStructure B₀ E).func F xs) =
      B₀.func
        (act.onFunc (projection act B₀ E).lang F)
        ((projection act B₀ E).toFun ∘ xs) := by
  have hxs :
      xs = fun _ => xs (UnaryFunctions.unaryIndex F) :=
    UnaryFunctions.unaryTuple_eq_constant F xs
  rw [hxs]
  simpa [projection, Function.comp_def] using
    projection_map_func_eq_constant
      act B₀ E F (xs (UnaryFunctions.unaryIndex F))

/-- Genericity of a subset of cycle-sparsening witness vertices. -/
def WitnessSetGeneric
    (S : Set (WitnessVertex B₀ E)) : Prop :=
  WitnessFamilyGeneric B₀ E (fun w : S => w.1)

/-- Projection is injective on every generic set of witness vertices. -/
theorem projection_injOn_of_generic
    (S : Set (WitnessVertex B₀ E))
    (hS : WitnessSetGeneric B₀ E S) :
    Set.InjOn
      (fun w => WitnessVertex.base B₀ E w) S := by
  intro w hw z hz hbase
  rcases w with ⟨x, W⟩
  rcases z with ⟨y, Z⟩
  change x = y at hbase
  subst y
  have hWZ : W = Z := by
    apply Subtype.ext
    funext t
    have hg :=
      hS ⟨⟨x, W⟩, hw⟩ ⟨⟨x, Z⟩, hz⟩ t t
    change
      AreGeneric B₀ E
        ⟨t.1, W.1 t⟩ ⟨t.1, Z.1 t⟩ at hg
    rcases hg with heq | ⟨hne, _⟩
    · exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    · exact (hne rfl).elim
  exact Sigma.ext rfl (heq_of_eq hWZ)

/-- **Claim `c:cycles:b`, generic part.** Projection is an embedding on
every generic subset of the cycle-sparsening witness. -/
theorem projection_isEmbeddingOn_of_generic
    (S : Set (WitnessVertex B₀ E))
    (hS : WitnessSetGeneric B₀ E S) :
    Structure.Homomorphism.IsEmbeddingOn act
      (projection act B₀ E) S := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw z hz h
    exact projection_injOn_of_generic B₀ E S hS hw hz h
  · intro n R xs hxs
    constructor
    · intro hrel
      refine ⟨?_, ?_⟩
      · simpa [projection, Function.comp_def] using hrel
      · intro i j y z
        exact hS ⟨xs i, hxs i⟩ ⟨xs j, hxs j⟩ y z
    · intro hrel
      simpa [projection, Function.comp_def] using hrel.1
  · intro n F xs hxs
    exact projection_map_func_eq act B₀ E F xs

end Sparsening
end AllThoseEPPA
