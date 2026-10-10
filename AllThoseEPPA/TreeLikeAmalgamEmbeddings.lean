import AllThoseEPPA.TreeLikeAmalgamStructure

/-!
# Exact source embeddings into the constructed Γ-free amalgam

The candidate amalgam structure contains precisely the union of
source relation tuples and function fibres. This file upgrades
the canonical source homomorphisms to **genuine embeddings**:
neither relations nor set-valued functions acquire spurious
values on a tuple from one source.

The essential reflection argument is not a cardinality argument.
If the tuple from B₁ has a representation from B₂, the exact
carrier-overlap lemma forces both tuples to come from C. The
checked relation and function equalities on C then show the
additional representation contributes no new information.
The argument is symmetric for B₂.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- Componentwise injectivity of the left inclusion. -/
theorem amalgamLeft_tuple_injective
    (f : I → X) (g : I → Y)
    {n : ℕ} {xs ys : Fin n → X}
    (h : amalgamLeft f g ∘ xs = amalgamLeft f g ∘ ys) :
    xs = ys := by
  funext i
  exact amalgamLeft_injective f g (congrFun h i)

/-- Componentwise injectivity of the right inclusion. -/
theorem amalgamRight_tuple_injective
    (f : I → X) (g : I → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    {n : ℕ} {xs ys : Fin n → Y}
    (h : amalgamRight f g ∘ xs = amalgamRight f g ∘ ys) :
    xs = ys := by
  funext i
  exact amalgamRight_injective f g hf hg (congrFun h i)

/-- The canonical inclusion of the first structure reflects and
preserves **all** relations and function fibres exactly. -/
noncomputable def amalgamLeftEmbedding
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang) :
    Structure.Embedding act B₁
      (amalgamStructure act f g hLang) where
  lang := 1
  toFun := amalgamLeft f.toFun g.toFun
  injective := amalgamLeft_injective f.toFun g.toFun
  map_rel_iff := by
    intro n R xs
    rw [act.onRel_one]
    change
      ((∃ xs' : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ xs' =
          amalgamLeft f.toFun g.toFun ∘ xs ∧ B₁.rel R xs') ∨
       (∃ ys : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ ys =
          amalgamLeft f.toFun g.toFun ∘ xs ∧ B₂.rel R ys))
        ↔ B₁.rel R xs
    constructor
    · rintro (⟨xs', hTuple, hRel⟩ | ⟨ys, hTuple, hRel⟩)
      · have hEq : xs' = xs :=
          amalgamLeft_tuple_injective f.toFun g.toFun hTuple
        simpa only [hEq] using hRel
      · obtain ⟨cs, hXs, hYs⟩ :=
          amalgam_tuple_overlap f.toFun g.toFun
            g.injective xs ys hTuple.symm
        rw [hYs] at hRel
        have hRel₁ :=
          (amalgam_overlap_relation act f g hLang R cs).mpr hRel
        simpa only [hXs] using hRel₁
    · intro hRel
      exact Or.inl ⟨xs, rfl, hRel⟩
  map_func := by
    intro n F xs
    rw [act.onFunc_one]
    ext z
    constructor
    · intro hz
      exact Or.inl ⟨xs, rfl, hz⟩
    · intro hz
      change
        (∃ xs' : Fin n → X,
          amalgamLeft f.toFun g.toFun ∘ xs' =
            amalgamLeft f.toFun g.toFun ∘ xs ∧
          z ∈ Structure.imageSet (amalgamLeft f.toFun g.toFun)
            (B₁.func F xs')) ∨
        (∃ ys : Fin n → Y,
          amalgamRight f.toFun g.toFun ∘ ys =
            amalgamLeft f.toFun g.toFun ∘ xs ∧
          z ∈ Structure.imageSet (amalgamRight f.toFun g.toFun)
            (B₂.func F ys)) at hz
      rcases hz with ⟨xs', hTuple, hz⟩ | ⟨ys, hTuple, hz⟩
      · have hEq : xs' = xs :=
          amalgamLeft_tuple_injective f.toFun g.toFun hTuple
        simpa only [hEq] using hz
      · obtain ⟨cs, hXs, hYs⟩ :=
          amalgam_tuple_overlap f.toFun g.toFun
            g.injective xs ys hTuple.symm
        rw [hYs] at hz
        rw [← amalgam_overlap_function act f g hLang F cs] at hz
        simpa only [hXs] using hz

/-- Symmetrically, the second source maps by an **exact embedding**
into the same concrete amalgam structure. -/
noncomputable def amalgamRightEmbedding
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang) :
    Structure.Embedding act B₂
      (amalgamStructure act f g hLang) where
  lang := 1
  toFun := amalgamRight f.toFun g.toFun
  injective :=
    amalgamRight_injective f.toFun g.toFun f.injective g.injective
  map_rel_iff := by
    intro n R ys
    rw [act.onRel_one]
    change
      ((∃ xs : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ xs =
          amalgamRight f.toFun g.toFun ∘ ys ∧ B₁.rel R xs) ∨
       (∃ ys' : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ ys' =
          amalgamRight f.toFun g.toFun ∘ ys ∧ B₂.rel R ys'))
        ↔ B₂.rel R ys
    constructor
    · rintro (⟨xs, hTuple, hRel⟩ | ⟨ys', hTuple, hRel⟩)
      · obtain ⟨cs, hXs, hYs⟩ :=
          amalgam_tuple_overlap f.toFun g.toFun
            g.injective xs ys hTuple
        rw [hXs] at hRel
        have hRel₂ :=
          (amalgam_overlap_relation act f g hLang R cs).mp hRel
        simpa only [hYs] using hRel₂
      · have hEq : ys' = ys :=
          amalgamRight_tuple_injective f.toFun g.toFun
            f.injective g.injective hTuple
        simpa only [hEq] using hRel
    · intro hRel
      exact Or.inr ⟨ys, rfl, hRel⟩
  map_func := by
    intro n F ys
    rw [act.onFunc_one]
    ext z
    constructor
    · intro hz
      exact Or.inr ⟨ys, rfl, hz⟩
    · intro hz
      change
        (∃ xs : Fin n → X,
          amalgamLeft f.toFun g.toFun ∘ xs =
            amalgamRight f.toFun g.toFun ∘ ys ∧
          z ∈ Structure.imageSet (amalgamLeft f.toFun g.toFun)
            (B₁.func F xs)) ∨
        (∃ ys' : Fin n → Y,
          amalgamRight f.toFun g.toFun ∘ ys' =
            amalgamRight f.toFun g.toFun ∘ ys ∧
          z ∈ Structure.imageSet (amalgamRight f.toFun g.toFun)
            (B₂.func F ys')) at hz
      rcases hz with ⟨xs, hTuple, hz⟩ | ⟨ys', hTuple, hz⟩
      · obtain ⟨cs, hXs, hYs⟩ :=
          amalgam_tuple_overlap f.toFun g.toFun
            g.injective xs ys hTuple
        rw [hXs] at hz
        rw [amalgam_overlap_function act f g hLang F cs] at hz
        simpa only [hYs] using hz
      · have hEq : ys' = ys :=
          amalgamRight_tuple_injective f.toFun g.toFun
            f.injective g.injective hTuple
        simpa only [hEq] using hz

/-- Both actual structure embeddings identify every point of
the gluing substructure, not just set-theoretically but as the
specified maps from the sources. -/
theorem amalgamSourceEmbeddings_agree
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang) (i : I) :
    amalgamLeftEmbedding act f g hLang (f i) =
      amalgamRightEmbedding act f g hLang (g i) :=
  (amalgamRight_glued f.toFun g.toFun g.injective i).symm

end TreeLike
end AllThoseEPPA
