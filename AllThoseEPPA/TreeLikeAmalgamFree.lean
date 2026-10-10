import AllThoseEPPA.Irreducible
import AllThoseEPPA.TreeLikeAmalgamEmbeddings
import AllThoseEPPA.TreeLikeEmbeddingRangeClosure

/-!
# A genuine free decomposition of the constructed Γ-amalgam

The preceding files built the actual finite glued carrier and
structure, and proved that both source maps are exact Γ-structure
embeddings. This module upgrades the construction to the
`Structure.FreeDecomposition` API.

When both source structures have a vertex outside the glued
interface, the two embedded images are proper, closed, cover
the entire amalgam, contain every relation tuple wholly on one
side, and admit no function value on a mixed-side tuple.

The requirement that both sides be nontrivial is exactly the
properness condition in `FreeDecomposition`; the underlying
amalgam exists without it, and trivial attachment can be
handled separately in the later tree construction.
-/

namespace AllThoseEPPA
namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- The explicitly constructed Γ-free amalgam carries an actual
free decomposition into the images of the canonical structure
embeddings. This includes **all** relation and function data,
not merely the E-graph.

Both source inclusions are required to be proper. Their common
intersection is exactly the gluing image by the previously
checked carrier-overlap theorem. -/
noncomputable def amalgamFreeDecomposition
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang)
    (hLeftExtra : ∃ x : X, x ∉ Set.range f.toFun)
    (hRightExtra : ∃ y : Y, y ∉ Set.range g.toFun) :
    (amalgamStructure act f g hLang).FreeDecomposition := by
  let D := amalgamStructure act f g hLang
  let l : Structure.Embedding act B₁ D :=
    amalgamLeftEmbedding act f g hLang
  let r : Structure.Embedding act B₂ D :=
    amalgamRightEmbedding act f g hLang
  refine
    { left := Set.range l.toFun
      right := Set.range r.toFun
      left_closed := l.range_isClosed act
      right_closed := r.range_isClosed act
      cover := ?_
      left_proper := ?_
      right_proper := ?_
      rel_local := ?_
      func_cross_empty := ?_ }
  · change
      Set.range (amalgamLeft f.toFun g.toFun) ∪
        Set.range (amalgamRight f.toFun g.toFun) = Set.univ
    exact amalgamCarrier_covered f.toFun g.toFun
  · rintro hUniv
    obtain ⟨y, hy⟩ := hRightExtra
    have hz :
        (Sum.inr (⟨y, hy⟩ : {t : Y // t ∉ Set.range g.toFun}) :
          AmalgamCarrier f.toFun g.toFun) ∈ Set.range l.toFun := by
      rw [hUniv]
      exact Set.mem_univ _
    obtain ⟨x, hx⟩ := hz
    change
      (Sum.inl x : AmalgamCarrier f.toFun g.toFun) =
        Sum.inr ⟨y, hy⟩ at hx
    cases hx
  · rintro hUniv
    obtain ⟨x, hx⟩ := hLeftExtra
    have hz : amalgamLeft f.toFun g.toFun x ∈
        Set.range r.toFun := by
      rw [hUniv]
      exact Set.mem_univ _
    obtain ⟨y, hy⟩ := hz
    have hEq :
        amalgamLeft f.toFun g.toFun x =
          amalgamRight f.toFun g.toFun y := hy.symm
    obtain ⟨i, hfi, _⟩ :=
      (amalgamLeft_eq_amalgamRight_iff
        f.toFun g.toFun g.injective x y).mp hEq
    exact hx ⟨i, hfi.symm⟩
  · intro n R xs hRel
    change
      (∃ ls : Fin n → X,
        amalgamLeft f.toFun g.toFun ∘ ls = xs ∧ B₁.rel R ls) ∨
      (∃ rs : Fin n → Y,
        amalgamRight f.toFun g.toFun ∘ rs = xs ∧ B₂.rel R rs)
      at hRel
    rcases hRel with ⟨ls, hEq, _⟩ | ⟨rs, hEq, _⟩
    · left
      intro i
      exact ⟨ls i, (congrFun hEq i).symm⟩
    · right
      intro i
      exact ⟨rs i, (congrFun hEq i).symm⟩
  · intro n F xs hCross
    ext z
    constructor
    · intro hz
      change
        (∃ ls : Fin n → X,
          amalgamLeft f.toFun g.toFun ∘ ls = xs ∧
          z ∈ Structure.imageSet (amalgamLeft f.toFun g.toFun)
            (B₁.func F ls)) ∨
        (∃ rs : Fin n → Y,
          amalgamRight f.toFun g.toFun ∘ rs = xs ∧
          z ∈ Structure.imageSet (amalgamRight f.toFun g.toFun)
            (B₂.func F rs))
        at hz
      rcases hz with ⟨ls, hEq, _⟩ | ⟨rs, hEq, _⟩
      · exact False.elim (hCross (Or.inl (fun i =>
          ⟨ls i, (congrFun hEq i).symm⟩)))
      · exact False.elim (hCross (Or.inr (fun i =>
          ⟨rs i, (congrFun hEq i).symm⟩)))
    · intro hz
      exact hz.elim

end TreeLike
end AllThoseEPPA
