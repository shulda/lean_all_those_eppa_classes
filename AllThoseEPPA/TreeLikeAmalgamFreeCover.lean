import AllThoseEPPA.Irreducible
import AllThoseEPPA.TreeLikeAmalgamEmbeddings
import AllThoseEPPA.TreeLikeEmbeddingRangeClosure

/-!
# Free covers and irreducible localization in arbitrary Γ-amalgams

The paper's recursive tree amalgamation allows the gluing
interface to equal one entire side. Such an attachment is
legitimate, but cannot be represented by `FreeDecomposition`,
which requires both sides to be proper.

A `FreeCover` retains precisely the structural parts of a free
decomposition -- closed sides, cover, relation locality, and
empty function fibres on cross-side tuples -- **without**
imposing properness. An irreducible substructure of a free
cover must lie entirely in one side: if it met both exclusive
sides, restricting the cover to it would produce an *actual
proper free decomposition*, contradicting irreducibility.

This provides the precise mechanism needed for the paper's
Observation `obs:tree-amalgamation_irreducible`, including
degenerate gluing steps.
-/

namespace AllThoseEPPA
namespace Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A possibly degenerate presentation as the free union of
two closed substructures. Unlike `FreeDecomposition`, either
side is permitted to equal the whole carrier. -/
structure FreeCover (B : Structure L V) where
  left : Set V
  right : Set V
  left_closed : B.IsClosed left
  right_closed : B.IsClosed right
  cover : left ∪ right = Set.univ
  rel_local :
    ∀ {n : ℕ} (R : L.RelSymbol n) (xs : Fin n → V),
      B.rel R xs →
        (∀ i, xs i ∈ left) ∨ (∀ i, xs i ∈ right)
  func_cross_empty :
    ∀ {n : ℕ} (F : L.FuncSymbol n) (xs : Fin n → V),
      ¬ ((∀ i, xs i ∈ left) ∨ (∀ i, xs i ∈ right)) →
        B.func F xs = ∅

/-- Every irreducible closed induced substructure of a free
cover lies wholly on one side, even when a gluing attachment
is degenerate. The proof constructs a *proper* decomposition
of the irreducible substructure from failure of both
containments. -/
theorem FreeCover.irreducible_subset_one_side
    (B : Structure L V) (d : B.FreeCover)
    (S : Set V) (hS : B.IsClosed S)
    (hirr : (B.induce S hS).IsIrreducible) :
    S ⊆ d.left ∨ S ⊆ d.right := by
  by_contra hcontain
  have hnleft : ¬ S ⊆ d.left := by
    intro hleft
    exact hcontain (Or.inl hleft)
  have hnright : ¬ S ⊆ d.right := by
    intro hright
    exact hcontain (Or.inr hright)
  let leftS : Set S := {x | x.1 ∈ d.left}
  let rightS : Set S := {x | x.1 ∈ d.right}
  have hleftClosed :
      (B.induce S hS).IsClosed leftS := by
    intro n F xs hxs y hy
    change y.1 ∈ d.left
    apply d.left_closed F (Subtype.val ∘ xs)
    · intro i
      exact hxs i
    · exact hy
  have hrightClosed :
      (B.induce S hS).IsClosed rightS := by
    intro n F xs hxs y hy
    change y.1 ∈ d.right
    apply d.right_closed F (Subtype.val ∘ xs)
    · intro i
      exact hxs i
    · exact hy
  have hcover : leftS ∪ rightS = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.1 ∈ d.left ∪ d.right := by
      rw [d.cover]
      exact Set.mem_univ x.1
    simpa [leftS, rightS] using hx
  have hleftProper : leftS ≠ Set.univ := by
    rcases Set.not_subset.mp hnleft with ⟨x, hxS, hxL⟩
    intro hall
    have hx : (⟨x, hxS⟩ : S) ∈ leftS := by
      rw [hall]
      exact Set.mem_univ _
    exact hxL hx
  have hrightProper : rightS ≠ Set.univ := by
    rcases Set.not_subset.mp hnright with ⟨x, hxS, hxR⟩
    intro hall
    have hx : (⟨x, hxS⟩ : S) ∈ rightS := by
      rw [hall]
      exact Set.mem_univ _
    exact hxR hx
  let dec : (B.induce S hS).FreeDecomposition :=
    { left := leftS
      right := rightS
      left_closed := hleftClosed
      right_closed := hrightClosed
      cover := hcover
      left_proper := hleftProper
      right_proper := hrightProper
      rel_local := by
        intro n R xs hrel
        have h := d.rel_local R (Subtype.val ∘ xs) hrel
        rcases h with hl | hr
        · left
          intro i
          exact hl i
        · right
          intro i
          exact hr i
      func_cross_empty := by
        intro n F xs hcross
        have hamb : B.func F (Subtype.val ∘ xs) = ∅ := by
          apply d.func_cross_empty F (Subtype.val ∘ xs)
          intro hside
          apply hcross
          rcases hside with hl | hr
          · left
            intro i
            exact hl i
          · right
            intro i
            exact hr i
        ext y
        change (y.1 ∈ B.func F (Subtype.val ∘ xs)) ↔
          y ∈ (∅ : Set S)
        rw [hamb]
        simp }
  exact hirr.false dec

end Structure

namespace TreeLike

universe u v w x y
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable {I : Type w} {X : Type x} {Y : Type y}

/-- Both source ranges form a free cover of the actual
Γ-amalgam structure, **without any properness assumptions**.
This is the side-locality invariant needed to analyse arbitrary
recursive tree amalgamations, including trivial attachments. -/
noncomputable def amalgamFreeCover
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang) :
    (amalgamStructure act f g hLang).FreeCover := by
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
      rel_local := ?_
      func_cross_empty := ?_ }
  · change
      Set.range (amalgamLeft f.toFun g.toFun) ∪
        Set.range (amalgamRight f.toFun g.toFun) = Set.univ
    exact amalgamCarrier_covered f.toFun g.toFun
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

/-- Every irreducible substructure of the concrete Γ-amalgam
is supported on one of the two source sides, including when
one entire source is identified with the interface. -/
theorem irreducible_in_amalgam_side
    (act : L.Action Γ)
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁)
    (g : Structure.Embedding act C B₂)
    (hLang : f.lang = g.lang)
    (S : Set (AmalgamCarrier f.toFun g.toFun))
    (hS : (amalgamStructure act f g hLang).IsClosed S)
    (hIrr :
      ((amalgamStructure act f g hLang).induce S hS).IsIrreducible) :
    S ⊆ Set.range (amalgamLeft f.toFun g.toFun) ∨
      S ⊆ Set.range (amalgamRight f.toFun g.toFun) := by
  exact Structure.FreeCover.irreducible_subset_one_side
    (amalgamStructure act f g hLang)
    (amalgamFreeCover act f g hLang) S hS hIrr

end TreeLike
end AllThoseEPPA
